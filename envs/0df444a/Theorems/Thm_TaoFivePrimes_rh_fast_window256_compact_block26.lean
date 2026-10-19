-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_compact_block26
-- name    : TaoFivePrimes.rh_fast_window256_compact_block26
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:59:59.920705+00:00
-- url     : https://prove2.me/theorems/7ef2acf8-178e-4dde-8ffb-3097ca15775f
-- title:
--   TaoFivePrimes.rh_fast_window256_compact_block26
-- statement:
--   All24 moment-output error budgets and reference magnitude bounds pass ordinary integer kernel checking at832<=j<864 with256-bit arithmetic and a lossless packed reference representation. Analytic interpretation and the final RH window are separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed reference data and surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference

theorem TaoFivePrimes.rh_fast_window256_compact_block26 : RHFastWindow256CompactReference.block 832 32=true := by sorry
