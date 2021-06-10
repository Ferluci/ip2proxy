// This ip2proxy package allows user to query an IP address if it was being used as
// VPN anonymizer, open proxies, web proxies, Tor exits, data center,
// web hosting (DCH) range, search engine robots (SES) and residential (RES)
// by using the IP2Proxy database.
package ip2proxy

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"math/big"
	"net"
	"os"
	"strconv"
)

type DBReader interface {
	io.ReadCloser
	io.ReaderAt
}

type InMemoryDBReader struct {
	*bytes.Reader
}

func (r *InMemoryDBReader) Close() error {
	return nil
}

type databaseMeta struct {
	databaseType      uint8
	databaseColumn    uint8
	databaseDay       uint8
	databaseMonth     uint8
	databaseYear      uint8
	ipv4databaseCount uint32
	ipv4databaseAddr  uint32
	ipv6databaseCount uint32
	ipv6databaseAddr  uint32
	ipv4indexBaseAddr uint32
	ipv6indexBaseAddr uint32
	ipv4columnSize    uint32
	ipv6columnSize    uint32
}

// The Record struct stores all of the available
// proxy info found in the IP2Proxy database.
type Record struct {
	CountryShort string
	CountryLong  string
	Region    string
	City      string
	Isp       string
	ProxyType string
	Domain    string
	UsageType string
	Asn       string
	As        string
	LastSeen  string
	Threat    string
	IsProxy   int8
}

type DB struct {
	f    DBReader
	meta databaseMeta

	countryPositionOffset   uint32
	regionPositionOffset    uint32
	cityPositionOffset      uint32
	ispPositionOffset       uint32
	proxyTypePositionOffset uint32
	domainPositionOffset    uint32
	usageTypePositionOffset uint32
	asnPositionOffset       uint32
	asPositionOffset        uint32
	lastSeenPositionOffset  uint32
	threatPositionOffset    uint32

	countryEnabled   bool
	regionEnabled    bool
	cityEnabled      bool
	ispEnabled       bool
	proxyTypeEnabled bool
	domainEnabled    bool
	usageTypeEnabled bool
	asnEnabled       bool
	asEnabled        bool
	lastSeenEnabled  bool
	threatEnabled    bool

	metaOk bool
}

var countryPosition = [11]uint8{0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3}
var regionPosition = [11]uint8{0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4}
var cityPosition = [11]uint8{0, 0, 0, 5, 5, 5, 5, 5, 5, 5, 5}
var ispPosition = [11]uint8{0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6}
var proxyTypePosition = [11]uint8{0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2}
var domainPosition = [11]uint8{0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7}
var usageTypePosition = [11]uint8{0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8}
var asnPosition = [11]uint8{0, 0, 0, 0, 0, 0, 0, 9, 9, 9, 9}
var asPosition = [11]uint8{0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10}
var lastSeenPosition = [11]uint8{0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 11}
var threatPosition = [11]uint8{0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12}

const moduleVersion string = "3.1.0"

var maxIpv4Range = big.NewInt(4294967295)
var maxIpv6Range = big.NewInt(0)
var fromV4mapped = big.NewInt(281470681743360)
var toV4mapped = big.NewInt(281474976710655)
var from6to4 = big.NewInt(0)
var to6to4 = big.NewInt(0)
var fromTeredo = big.NewInt(0)
var toTeredo = big.NewInt(0)
var last32bits = big.NewInt(4294967295)

const countryShort uint32 = 0x00001
const countryLong uint32 = 0x00002
const region uint32 = 0x00004
const city uint32 = 0x00008
const isp uint32 = 0x00010
const proxyType uint32 = 0x00020
const isProxy uint32 = 0x00040
const domain uint32 = 0x00080
const usageType uint32 = 0x00100
const asn uint32 = 0x00200
const as uint32 = 0x00400
const lastSeen uint32 = 0x00800
const threat uint32 = 0x01000

const all = countryShort | countryLong | region | city | isp | proxyType | isProxy | domain | usageType | asn | as | lastSeen | threat

const msgNotSupported string = "NOT SUPPORTED"
const msgInvalidIp string = "INVALID IP ADDRESS"
const msgMissingFile string = "MISSING FILE"
const msgIpv6Unsupported string = "IPV6 ADDRESS MISSING IN IPV4 BIN"

// get IP type and calculate IP number; calculates index too if exists
func (d *DB) checkIP(ip string) (ipType uint32, ipNum *big.Int, ipIndex uint32) {
	ipType = 0
	ipNum = big.NewInt(0)
	ipNumTmp := big.NewInt(0)
	ipIndex = 0
	ipaddress := net.ParseIP(ip)

	if ipaddress != nil {
		v4 := ipaddress.To4()

		if v4 != nil {
			ipType = 4
			ipNum.SetBytes(v4)
		} else {
			v6 := ipaddress.To16()

			if v6 != nil {
				ipType = 6
				ipNum.SetBytes(v6)

				if ipNum.Cmp(fromV4mapped) >= 0 && ipNum.Cmp(toV4mapped) <= 0 {
					// ipv4-mapped ipv6 should treat as ipv4 and read ipv4 data section
					ipType = 4
					ipNum.Sub(ipNum, fromV4mapped)
				} else if ipNum.Cmp(from6to4) >= 0 && ipNum.Cmp(to6to4) <= 0 {
					// 6to4 so need to remap to ipv4
					ipType = 4
					ipNum.Rsh(ipNum, 80)
					ipNum.And(ipNum, last32bits)
				} else if ipNum.Cmp(fromTeredo) >= 0 && ipNum.Cmp(toTeredo) <= 0 {
					// Teredo so need to remap to ipv4
					ipType = 4
					ipNum.Not(ipNum)
					ipNum.And(ipNum, last32bits)
				}
			}
		}
	}
	if ipType == 4 {
		if d.meta.ipv4indexBaseAddr > 0 {
			ipNumTmp.Rsh(ipNum, 16)
			ipNumTmp.Lsh(ipNumTmp, 3)
			ipIndex = uint32(ipNumTmp.Add(ipNumTmp, big.NewInt(int64(d.meta.ipv4indexBaseAddr))).Uint64())
		}
	} else if ipType == 6 {
		if d.meta.ipv6indexBaseAddr > 0 {
			ipNumTmp.Rsh(ipNum, 112)
			ipNumTmp.Lsh(ipNumTmp, 3)
			ipIndex = uint32(ipNumTmp.Add(ipNumTmp, big.NewInt(int64(d.meta.ipv6indexBaseAddr))).Uint64())
		}
	}
	return
}

// read byte
func (d *DB) readUint8(pos int64) (uint8, error) {
	var result uint8
	data := make([]byte, 1)
	_, err := d.f.ReadAt(data, pos-1)
	if err != nil {
		return 0, err
	}
	result = data[0]
	return result, nil
}

// read unsigned 32-bit integer from slices
func (d *DB) readUint32Row(row []byte, pos uint32) uint32 {
	var result uint32
	data := row[pos : pos+4]
	result = binary.LittleEndian.Uint32(data)
	return result
}

// read unsigned 32-bit integer
func (d *DB) readUint32(pos uint32) (uint32, error) {
	pos2 := int64(pos)
	var result uint32
	data := make([]byte, 4)
	_, err := d.f.ReadAt(data, pos2-1)
	if err != nil {
		return 0, err
	}
	buf := bytes.NewReader(data)
	err = binary.Read(buf, binary.LittleEndian, &result)
	if err != nil {
		fmt.Printf("binary read failed: %v", err)
	}
	return result, nil
}

// read unsigned 128-bit integer
func (d *DB) readUint128(pos uint32) (*big.Int, error) {
	pos2 := int64(pos)
	result := big.NewInt(0)
	data := make([]byte, 16)
	_, err := d.f.ReadAt(data, pos2-1)
	if err != nil {
		return nil, err
	}

	// little endian to big endian
	for i, j := 0, len(data)-1; i < j; i, j = i+1, j-1 {
		data[i], data[j] = data[j], data[i]
	}
	result.SetBytes(data)
	return result, nil
}

// read string
func (d *DB) readStr(pos uint32) (string, error) {
	pos2 := int64(pos)
	var result string
	lenByte := make([]byte, 1)
	_, err := d.f.ReadAt(lenByte, pos2)
	if err != nil {
		return "", err
	}
	strLen := lenByte[0]
	data := make([]byte, strLen)
	_, err = d.f.ReadAt(data, pos2+1)
	if err != nil {
		return "", err
	}
	result = string(data[:strLen])
	return result, nil
}

// read float from slices
func (d *DB) readFloatRow(row []byte, pos uint32) float32 {
	var result float32
	data := row[pos : pos+4]
	bits := binary.LittleEndian.Uint32(data)
	result = math.Float32frombits(bits)
	return result
}

// read float
func (d *DB) readFloat(pos uint32) (float32, error) {
	pos2 := int64(pos)
	var retVal float32
	data := make([]byte, 4)
	_, err := d.f.ReadAt(data, pos2-1)
	if err != nil {
		return 0, err
	}
	buf := bytes.NewReader(data)
	err = binary.Read(buf, binary.LittleEndian, &retVal)
	if err != nil {
		fmt.Printf("binary read failed: %v", err)
	}
	return retVal, nil
}

func fatal(db *DB, err error) (*DB, error) {
	_ = db.f.Close()
	return nil, err
}


// OpenInMemoryDB takes the path to the IP2Proxy BIN database file. It will read all file data
// and return the underlining DB object.
func OpenInMemoryDB(dbpath string) (*DB, error) {
	dbFile, err := os.Open(dbpath)
	defer dbFile.Close()

	if err != nil {
		return nil, err
	}

	info, err := dbFile.Stat()
	if err != nil {
		return nil, err
	}

	// calculate the bytes size
	var size = info.Size()
	fileData := make([]byte, size)

	// read into buffer
	buffer := bufio.NewReader(dbFile)
	_, err = buffer.Read(fileData)

	return OpenDBWithReader(&InMemoryDBReader{bytes.NewReader(fileData)})
}

// OpenDB takes the path to the IP2Proxy BIN database file. It will read all the metadata required to
// be able to extract the embedded proxy data, and return the underlining DB object.
func OpenDB(dbpath string) (*DB, error) {
	f, err := os.Open(dbpath)
	if err != nil {
		return nil, err
	}

	return OpenDBWithReader(f)
}

// OpenDBWithReader takes a DBReader to the IP2Proxy BIN database file. It will read all the metadata required to
// be able to extract the embedded proxy data, and return the underlining DB object.
func OpenDBWithReader(reader DBReader) (*DB, error) {
	var db = &DB{}

	maxIpv6Range.SetString("340282366920938463463374607431768211455", 10)
	from6to4.SetString("42545680458834377588178886921629466624", 10)
	to6to4.SetString("42550872755692912415807417417958686719", 10)
	fromTeredo.SetString("42540488161975842760550356425300246528", 10)
	toTeredo.SetString("42540488241204005274814694018844196863", 10)

	db.f = reader

	var err error
	db.meta.databaseType, err = db.readUint8(1)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.databaseColumn, err = db.readUint8(2)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.databaseYear, err = db.readUint8(3)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.databaseMonth, err = db.readUint8(4)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.databaseDay, err = db.readUint8(5)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv4databaseCount, err = db.readUint32(6)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv4databaseAddr, err = db.readUint32(10)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv6databaseCount, err = db.readUint32(14)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv6databaseAddr, err = db.readUint32(18)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv4indexBaseAddr, err = db.readUint32(22)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv6indexBaseAddr, err = db.readUint32(26)
	if err != nil {
		return fatal(db, err)
	}
	db.meta.ipv4columnSize = uint32(db.meta.databaseColumn << 2)              // 4 bytes each column
	db.meta.ipv6columnSize = uint32(16 + ((db.meta.databaseColumn - 1) << 2)) // 4 bytes each column, except IPFrom column which is 16 bytes

	dbt := db.meta.databaseType

	if countryPosition[dbt] != 0 {
		db.countryPositionOffset = uint32(countryPosition[dbt]-2) << 2
		db.countryEnabled = true
	}
	if regionPosition[dbt] != 0 {
		db.regionPositionOffset = uint32(regionPosition[dbt]-2) << 2
		db.regionEnabled = true
	}
	if cityPosition[dbt] != 0 {
		db.cityPositionOffset = uint32(cityPosition[dbt]-2) << 2
		db.cityEnabled = true
	}
	if ispPosition[dbt] != 0 {
		db.ispPositionOffset = uint32(ispPosition[dbt]-2) << 2
		db.ispEnabled = true
	}
	if proxyTypePosition[dbt] != 0 {
		db.proxyTypePositionOffset = uint32(proxyTypePosition[dbt]-2) << 2
		db.proxyTypeEnabled = true
	}
	if domainPosition[dbt] != 0 {
		db.domainPositionOffset = uint32(domainPosition[dbt]-2) << 2
		db.domainEnabled = true
	}
	if usageTypePosition[dbt] != 0 {
		db.usageTypePositionOffset = uint32(usageTypePosition[dbt]-2) << 2
		db.usageTypeEnabled = true
	}
	if asnPosition[dbt] != 0 {
		db.asnPositionOffset = uint32(asnPosition[dbt]-2) << 2
		db.asnEnabled = true
	}
	if asPosition[dbt] != 0 {
		db.asPositionOffset = uint32(asPosition[dbt]-2) << 2
		db.asEnabled = true
	}
	if lastSeenPosition[dbt] != 0 {
		db.lastSeenPositionOffset = uint32(lastSeenPosition[dbt]-2) << 2
		db.lastSeenEnabled = true
	}
	if threatPosition[dbt] != 0 {
		db.threatPositionOffset = uint32(threatPosition[dbt]-2) << 2
		db.threatEnabled = true
	}

	db.metaOk = true

	return db, nil
}

// ModuleVersion returns the version of the component.
func ModuleVersion() string {
	return moduleVersion
}

// PackageVersion returns the database type.
func (d *DB) PackageVersion() string {
	return strconv.Itoa(int(d.meta.databaseType))
}

// DatabaseVersion returns the database version.
func (d *DB) DatabaseVersion() string {
	return "20" + strconv.Itoa(int(d.meta.databaseYear)) + "." + strconv.Itoa(int(d.meta.databaseMonth)) + "." + strconv.Itoa(int(d.meta.databaseDay))
}

// populate record with message
func loadMessage(mesg string) Record {
	var x Record

	x.CountryShort = mesg
	x.CountryLong = mesg
	x.Region = mesg
	x.City = mesg
	x.Isp = mesg
	x.ProxyType = mesg
	x.Domain = mesg
	x.UsageType = mesg
	x.Asn = mesg
	x.As = mesg
	x.LastSeen = mesg
	x.Threat = mesg
	x.IsProxy = -1

	return x
}

// GetAll will return all proxy fields based on the queried IP address.
func (d *DB) GetAll(ipaddress string) (map[string]string, error) {
	data, err := d.query(ipaddress, all)

	var x = make(map[string]string)
	s := strconv.Itoa(int(data.IsProxy))
	x["isProxy"] = s
	x["ProxyType"] = data.ProxyType
	x["CountryShort"] = data.CountryShort
	x["CountryLong"] = data.CountryLong
	x["Region"] = data.Region
	x["City"] = data.City
	x["ISP"] = data.Isp
	x["Domain"] = data.Domain
	x["UsageType"] = data.UsageType
	x["ASN"] = data.Asn
	x["AS"] = data.As
	x["LastSeen"] = data.LastSeen
	x["Threat"] = data.Threat

	return x, err
}

// GetCountryShort will return the ISO-3166 country code based on the queried IP address.
func (d *DB) GetCountryShort(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, countryShort)
	return data.CountryShort, err
}

// GetCountryLong will return the country name based on the queried IP address.
func (d *DB) GetCountryLong(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, countryLong)
	return data.CountryLong, err
}

// GetRegion will return the region name based on the queried IP address.
func (d *DB) GetRegion(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, region)
	return data.Region, err
}

// GetCity will return the city name based on the queried IP address.
func (d *DB) GetCity(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, city)
	return data.City, err
}

// GetIsp will return the Internet Service Provider name based on the queried IP address.
func (d *DB) GetIsp(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, isp)
	return data.Isp, err
}

// GetProxyType will return the proxy type based on the queried IP address.
func (d *DB) GetProxyType(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, proxyType)
	return data.ProxyType, err
}

// GetDomain will return the domain name based on the queried IP address.
func (d *DB) GetDomain(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, domain)
	return data.Domain, err
}

// GetUsageType will return the usage type based on the queried IP address.
func (d *DB) GetUsageType(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, usageType)
	return data.UsageType, err
}

// GetAsn will return the autonomous system number based on the queried IP address.
func (d *DB) GetAsn(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, asn)
	return data.Asn, err
}

// GetAs will return the autonomous system name based on the queried IP address.
func (d *DB) GetAs(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, as)
	return data.As, err
}

// GetLastSeen will return the number of days that the proxy was last seen based on the queried IP address.
func (d *DB) GetLastSeen(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, lastSeen)
	return data.LastSeen, err
}

// GetThreat will return the threat type of the proxy.
func (d *DB) GetThreat(ipaddress string) (string, error) {
	data, err := d.query(ipaddress, threat)
	return data.Threat, err
}

// GetShort will return: -1 (errors), 0 (not a proxy), 1 (a proxy), 2 (a data center IP address or search engine robot).
func (d *DB) GetShort(ipaddress string) (int8, error) {
	data, err := d.query(ipaddress, isProxy)
	return data.IsProxy, err
}

// IsProxy checks whether the queried IP address was a proxy.
func (d *DB) IsProxy(ipaddress string) (bool, error) {
	data, err := d.query(ipaddress, isProxy)
	if err != nil {
		return false, err
	}
	if data.IsProxy > 0 {
		return true, nil
	}
	return false, nil
}

// main query
func (d *DB) query(ipaddress string, mode uint32) (Record, error) {
	x := loadMessage(msgNotSupported) // default message

	// read metadata
	if !d.metaOk {
		x = loadMessage(msgMissingFile)
		return x, nil
	}

	// check IP type and return IP number & index (if exists)
	iptype, ipno, ipindex := d.checkIP(ipaddress)

	if iptype == 0 {
		x = loadMessage(msgInvalidIp)
		return x, nil
	}

	var err error
	var colSize uint32
	var baseAddr uint32
	var low uint32
	var high uint32
	var mid uint32
	var rowOffset uint32
	var rowOffset2 uint32
	var countryPos uint32
	ipFrom := big.NewInt(0)
	ipTo := big.NewInt(0)
	maxIP := big.NewInt(0)

	if iptype == 4 {
		baseAddr = d.meta.ipv4databaseAddr
		high = d.meta.ipv4databaseCount
		maxIP = maxIpv4Range
		colSize = d.meta.ipv4columnSize
	} else {
		if d.meta.ipv6databaseCount == 0 {
			x = loadMessage(msgIpv6Unsupported)
			return x, nil
		}
		baseAddr = d.meta.ipv6databaseAddr
		high = d.meta.ipv6databaseCount
		maxIP = maxIpv6Range
		colSize = d.meta.ipv6columnSize
	}

	// reading index
	if ipindex > 0 {
		low, err = d.readUint32(ipindex)
		if err != nil {
			return x, err
		}
		high, err = d.readUint32(ipindex + 4)
		if err != nil {
			return x, err
		}
	}

	if ipno.Cmp(maxIP) >= 0 {
		ipno.Sub(ipno, big.NewInt(1))
	}

	for low <= high {
		mid = (low + high) >> 1
		rowOffset = baseAddr + (mid * colSize)
		rowOffset2 = rowOffset + colSize

		if iptype == 4 {
			ipfrom32, err := d.readUint32(rowOffset)
			if err != nil {
				return x, err
			}
			ipFrom = big.NewInt(int64(ipfrom32))

			ipto32, err := d.readUint32(rowOffset2)
			if err != nil {
				return x, err
			}
			ipTo = big.NewInt(int64(ipto32))
		} else {
			ipFrom, err = d.readUint128(rowOffset)
			if err != nil {
				return x, err
			}

			ipTo, err = d.readUint128(rowOffset2)
			if err != nil {
				return x, err
			}
		}

		if ipno.Cmp(ipFrom) >= 0 && ipno.Cmp(ipTo) < 0 {
			var firstcol uint32 = 4 // 4 bytes for ip from
			if iptype == 6 {
				firstcol = 16 // 16 bytes for ipv6
			}

			row := make([]byte, colSize-firstcol) // exclude the ip from field
			_, err := d.f.ReadAt(row, int64(rowOffset+firstcol-1))
			if err != nil {
				return x, err
			}

			if d.proxyTypeEnabled {
				if mode&proxyType != 0 || mode&isProxy != 0 {
					if x.ProxyType, err = d.readStr(d.readUint32Row(row, d.proxyTypePositionOffset)); err != nil {
						return x, err
					}
				}
			}

			if d.countryEnabled {
				if mode&countryShort != 0 || mode&countryLong != 0 || mode&isProxy != 0 {
					countryPos = d.readUint32Row(row, d.countryPositionOffset)
				}
				if mode&countryShort != 0 || mode&isProxy != 0 {
					if x.CountryShort, err = d.readStr(countryPos); err != nil {
						return x, err
					}
				}
				if mode&countryLong != 0 {
					if x.CountryLong, err = d.readStr(countryPos + 3); err != nil {
						return x, err
					}
				}
			}

			if mode&region != 0 && d.regionEnabled {
				if x.Region, err = d.readStr(d.readUint32Row(row, d.regionPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&city != 0 && d.cityEnabled {
				if x.City, err = d.readStr(d.readUint32Row(row, d.cityPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&isp != 0 && d.ispEnabled {
				if x.Isp, err = d.readStr(d.readUint32Row(row, d.ispPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&domain != 0 && d.domainEnabled {
				if x.Domain, err = d.readStr(d.readUint32Row(row, d.domainPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&usageType != 0 && d.usageTypeEnabled {
				if x.UsageType, err = d.readStr(d.readUint32Row(row, d.usageTypePositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&asn != 0 && d.asnEnabled {
				if x.Asn, err = d.readStr(d.readUint32Row(row, d.asnPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&as != 0 && d.asEnabled {
				if x.As, err = d.readStr(d.readUint32Row(row, d.asPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&lastSeen != 0 && d.lastSeenEnabled {
				if x.LastSeen, err = d.readStr(d.readUint32Row(row, d.lastSeenPositionOffset)); err != nil {
					return x, err
				}
			}

			if mode&threat != 0 && d.threatEnabled {
				if x.Threat, err = d.readStr(d.readUint32Row(row, d.threatPositionOffset)); err != nil {
					return x, err
				}
			}

			if x.CountryShort == "-" || x.ProxyType == "-" {
				x.IsProxy = 0
			} else {
				if x.ProxyType == "DCH" || x.ProxyType == "SES" {
					x.IsProxy = 2
				} else {
					x.IsProxy = 1
				}
			}

			return x, nil
		} else {
			if ipno.Cmp(ipFrom) < 0 {
				high = mid - 1
			} else {
				low = mid + 1
			}
		}
	}
	return x, nil
}

func (d *DB) Close() error {
	err := d.f.Close()
	return err
}
