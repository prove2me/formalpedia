-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_new256_packed_reference_lookup
-- name    : TaoFivePrimes.rh_batch01_new256_packed_reference_lookup
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T15:51:42.423227+00:00
-- url     : https://prove2.me/theorems/fe4f3ac1-fa0d-4cfe-bf66-71a7caacf94c
-- title:
--   TaoFivePrimes.rh_batch01_new256_packed_reference_lookup
-- statement:
--   Ordinary proof of the fresh-center packed reference lookup. Numerical arithmetic remains a separate required input.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original mathematical attribution: sometik179, submission c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_packed_reference_equality

theorem TaoFivePrimes.rh_batch01_new256_packed_reference_lookup (k j:Nat) (hk:k<24) (hj:j<2048) :
 RHBatch01New256CompactReference.signed k j=RHBatch01ZetaCorrelation.signed (RHBatch01GammaFourierTable.values k) j := by sorry
