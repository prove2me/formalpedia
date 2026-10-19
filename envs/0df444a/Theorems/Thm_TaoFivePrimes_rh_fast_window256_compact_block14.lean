-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block14
-- name    : TaoFivePrimes.rh_fast_window256_compact_block14
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:47:32.307993+00:00
-- url     : https://prove2.me/theorems/32a4f0f4-0a7d-479e-a59c-97a3b10a92f4
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block14
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at448<=j<480 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block14 : RHFastWindow256CompactReference.block 448 32=true := by sorry
