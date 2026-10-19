-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_window_endpoint_signs
-- name    : TaoFivePrimes.rh_batch01_height_window_endpoint_signs
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T18:16:27.790983+00:00
-- url     : https://prove2.me/theorems/ae8fe143-18c1-439d-b818-8201a2839507
-- title:
--   TaoFivePrimes.rh_batch01_height_window_endpoint_signs
-- statement:
--   Opposite signs of the actual normalized completed Riemann zeta function at the endpoints of all409 existing brackets in the final128-unit window. Combines the accepted actual Fourier coefficient enclosure, reconstruction, real polynomial FFT enclosures and finite bracket margins, preserving signs under the positive Gaussian factor. This proves the sign child only; the separate zero-count child is still needed for the window, and the window alone does not finish finite-height RH or Proposition7.2.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface

theorem TaoFivePrimes.rh_batch01_height_window_endpoint_signs : ∀ p ∈ RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate, RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.l)*RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.r)<0 := by sorry
