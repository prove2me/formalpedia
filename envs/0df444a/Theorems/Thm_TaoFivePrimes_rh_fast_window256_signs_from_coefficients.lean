-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_window256_signs_from_coefficients
-- name    : TaoFivePrimes.rh_fast_window256_signs_from_coefficients
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T11:22:49.19543+00:00
-- url     : https://prove2.me/theorems/05adec28-fbdd-4a43-89ea-a5dbb756fd18
-- title:
--   TaoFivePrimes.rh_fast_window256_signs_from_coefficients
-- statement:
--   Explicit1e-14 window coefficient accuracy implies actual opposite normalized-zeta signs on all409 accepted geometric brackets. No closed coefficient accuracy or old window theorem is assumed.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_window256_signs_from_coefficients
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 : ∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate, RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by sorry
