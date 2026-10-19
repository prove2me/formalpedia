-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_upper_right_endpoint
-- name    : TaoFivePrimes.rh_batch01_height_upper_right_endpoint
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:11:41.436169+00:00
-- url     : https://prove2.me/theorems/72c933bf-1d4b-4bd2-8e4a-e793d4c3ba24
-- title:
--   TaoFivePrimes.rh_batch01_height_upper_right_endpoint
-- statement:
--   All eight horizontal Taylor jets at the far-right upper endpoint are certified directly from the accepted proposed-spectrum coefficient errors and eight exact integer sums. Each stored endpoint differs from its2049-word spectrum sum by at most4 units at2^80 scale; the actual analytic sum error is at most2048e-21. This avoids an unused third full FFT grid. No winding, count, or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourGridV2
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet

theorem TaoFivePrimes.rh_batch01_height_upper_right_endpoint (k : Nat) (hk:k<8) :
 ‖RHBatch01PolynomialJet.jet (64+Complex.I/2) (1/32) k-
 RHHighContourVector.value (RHBatch01ContourGrid.horizontal 4096 k)‖≤1/10^12 := by sorry
