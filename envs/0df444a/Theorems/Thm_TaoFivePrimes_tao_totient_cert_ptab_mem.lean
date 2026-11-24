-- Prove2me | Theorems.Thm_TaoFivePrimes_tao_totient_cert_ptab_mem
-- name    : TaoFivePrimes.tao_totient_cert_ptab_mem
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:45:09.033045+00:00
-- url     : https://prove2.me/theorems/ad9be8fe-98ca-449e-8239-13303cd915e9
-- title:
--   Each certificate prime belongs to the theta certificate list
-- statement:
--   The Chebyshev-theta certificates used in this development are indexed by the `Finset` `plist`, the list of the 66 primes below 320. The certificate prime table `ptab` records the same primes in increasing order.
--
--   The theorem states that every entry of the table is a member of the certificate list:
--   $$ \mathrm{ptab}(i) \;\in\; \mathrm{plist} \qquad (0 \le i < 66). $$
--
--   Combined with the identification $\mathrm{ptab}(i) = p_{i+1}$, this lets arguments about the first 66 primes pass freely between the explicit numeric table and the certificate list `plist`, so that the prime-by-prime logarithm certificates can be attached to the entries of `ptab`.
-- source:
--   Input data for the finite Rosser--Schoenfeld (1962) totient verification formalized in this project; the list `plist` is the prime list of the Chebyshev-theta logarithm certificates.

import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Definitions.Def_TaoFivePrimes_totient_cert_tables

namespace TaoFivePrimes

theorem tao_totient_cert_ptab_mem (i : ℕ) (hi : i < 66) :
    ptab i ∈ plist := by sorry

end TaoFivePrimes
