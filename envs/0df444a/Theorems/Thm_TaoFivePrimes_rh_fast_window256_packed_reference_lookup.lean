-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_packed_reference_lookup
-- name    : TaoFivePrimes.rh_fast_window256_packed_reference_lookup
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:08:10.549985+00:00
-- url     : https://prove2.me/theorems/aab90362-e694-4e75-8730-bc123717ee1d
-- title:
--   TaoFivePrimes.rh_fast_window256_packed_reference_lookup
-- statement:
--   Every signed proposed value extracted from the packed reference representation equals the corresponding original table value at k<24 and j<2048.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable

theorem TaoFivePrimes.rh_fast_window256_packed_reference_lookup (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHFastWindow256CompactReference.signed k j=RHHighZetaCorrelation.signed (RHHighGammaFourierTable.values k) j := by sorry
