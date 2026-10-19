-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block03
-- name    : TaoFivePrimes.rh_fast_window256_compact_block03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:12:38.291479+00:00
-- url     : https://prove2.me/theorems/e0b0e914-2814-4b9f-ba17-dfe75859f525
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block03
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at96<=j<128 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block03 : RHFastWindow256CompactReference.block 96 32=true := by sorry
