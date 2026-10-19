-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_window_count_le
-- name    : TaoFivePrimes.rh_batch01_height_window_count_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T18:19:40.148887+00:00
-- url     : https://prove2.me/theorems/5834eec8-356c-4cde-8875-549d24bb4418
-- title:
--   TaoFivePrimes.rh_batch01_height_window_count_le
-- statement:
--   At most409 actual nontrivial zeta zeros in the exact closed128-unit window. Applies the accepted concrete finite-record count proof to the accepted all-grid accuracy theorem, discharging its final explicit hypothesis. The separate opposite-sign theorem is also required for the window; full finite-height RH and Proposition7.2 remain separate.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow

theorem TaoFivePrimes.rh_batch01_height_window_count_le : (RHHighHeight.windowZeros 3289999744 3289999872).ncard ≤ 409 := by sorry
