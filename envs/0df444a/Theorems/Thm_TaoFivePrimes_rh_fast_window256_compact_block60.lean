-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block60
-- name    : TaoFivePrimes.rh_fast_window256_compact_block60
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T12:33:08.717272+00:00
-- url     : https://prove2.me/theorems/33b97dae-6576-485b-9429-04f467c25660
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block60
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at1920<=j<1952 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block60 : RHFastWindow256CompactReference.block 1920 32=true := by sorry
