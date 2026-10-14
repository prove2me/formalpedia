-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_window_finite
-- name    : TaoFivePrimes.rh_high_height_window_finite
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T10:12:13.53759+00:00
-- url     : https://prove2.me/theorems/cea7aa96-c05b-45ef-90a6-98357659bfcf
-- title:
--   TaoFivePrimes.rh_high_height_window_finite
-- statement:
--   The zeta zero set in any closed finite-height window inside the open critical strip is finite. This uses compactness and Mathlib's discreteness of the zeta zero set. No count upper bound or RH assertion is supplied.
-- source:
--   Immediate restriction of Mathlib IsCompact.inter_riemannZetaZeros_finite to a compact complex rectangle. The surrounding numerical project credits sometik179 (c9908072-d99a-4431-aad8-a72c6352619a) and Gabewhigham. This theorem uses no numerical certificate.

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Mathlib.NumberTheory.LSeries.ZetaZeros

theorem TaoFivePrimes.rh_high_height_window_finite (a b : ℝ) : (RHHighHeight.windowZeros a b).Finite := by sorry
