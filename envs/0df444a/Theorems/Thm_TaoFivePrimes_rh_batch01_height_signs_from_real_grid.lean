-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_signs_from_real_grid
-- name    : TaoFivePrimes.rh_batch01_height_signs_from_real_grid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T18:02:31.528666+00:00
-- url     : https://prove2.me/theorems/a68f4df4-e776-4c79-bad6-07b7ec02d95e
-- title:
--   TaoFivePrimes.rh_batch01_height_signs_from_real_grid
-- statement:
--   The accepted409 finite integer sign and margin checks imply signs of the normalized completed zeta function, provided the actual Gaussian window values are within1e-9 of the real FFT data. Proves the positive Gaussian scaling identity and preserves opposite signs under explicit error margins. The analytic grid enclosures remain explicit hypotheses.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01CoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface
import Definitions.Def_TaoFivePrimes_RHBatch01RealGrid

theorem TaoFivePrimes.rh_batch01_height_signs_from_real_grid
 (hgrid:∀i:Nat,i<4096 →
 |(RHBatch01FullCoefficient.W (-64+(i:ℝ)/32)).re-(RHBatch01RealGrid.value i:ℝ)/(2:ℝ)^80|≤1/10^9) :
 ∀p∈RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate,
 RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.l)*RHHighHeight.normalized (RHBatch01HeightBracketInterface.point p.r)<0 := by sorry
