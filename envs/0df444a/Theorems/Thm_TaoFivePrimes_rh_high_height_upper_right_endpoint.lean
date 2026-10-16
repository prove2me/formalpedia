-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_upper_right_endpoint
-- name    : TaoFivePrimes.rh_high_height_upper_right_endpoint
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T13:25:25.689625+00:00
-- url     : https://prove2.me/theorems/2fb684be-ea23-491c-801a-9d75cbcb5cb7
-- title:
--   TaoFivePrimes.rh_high_height_upper_right_endpoint
-- statement:
--   All eight horizontal Taylor jets at the far-right upper endpoint are certified directly from the accepted proposed-spectrum coefficient errors and eight exact integer sums. Each stored endpoint differs from its2049-word spectrum sum by at most4 units at2^80 scale; the actual analytic sum error is at most2048e-21. This avoids an unused third full FFT grid. No winding, count, or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourGridV2
import Definitions.Def_TaoFivePrimes_RHHighPolynomialJet

theorem TaoFivePrimes.rh_high_height_upper_right_endpoint (k : Nat) (hk:k<8) :
 ‖RHHighPolynomialJet.jet (64+Complex.I/2) (1/32) k-
 RHHighContourVector.value (RHHighContourGrid.horizontal 4096 k)‖≤1/10^12 := by sorry
