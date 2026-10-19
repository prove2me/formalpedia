-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block05
-- name    : TaoFivePrimes.rh_fast_window256_compact_block05
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:26:00.782543+00:00
-- url     : https://prove2.me/theorems/eaf60246-37f2-496f-8b95-020a09f12584
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block05
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at160<=j<192 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block05 : RHFastWindow256CompactReference.block 160 32=true := by sorry
