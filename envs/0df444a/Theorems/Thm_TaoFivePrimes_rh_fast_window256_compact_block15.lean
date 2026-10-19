-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block15
-- name    : TaoFivePrimes.rh_fast_window256_compact_block15
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:48:01.002063+00:00
-- url     : https://prove2.me/theorems/edafe3fb-fb89-4741-a1a0-b85f21849f99
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block15
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at480<=j<512 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block15 : RHFastWindow256CompactReference.block 480 32=true := by sorry
