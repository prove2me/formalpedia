-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_standardFormCriterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.standardFormCriterion
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:38:29.746048+00:00
-- url     : https://prove2.me/theorems/7cf24f21-6a7c-4251-b13d-4de3fe464ca1
-- title:
--   Explicit standard-form Simon inequality
-- statement:
--   For arbitrary real $a,b,c_1,c_2$, let $V_0$ have diagonal $(a,a,b,b)$ and only the symmetric off-diagonal correlations $(V_0)_{13}=c_1$, $(V_0)_{24}=c_2$. Write its mode blocks as $A,B,C$, and put $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. The invariant condition $\det A\det B+(1/4-|\det C|)^2-\operatorname{tr}(AJCJBJC^TJ)\ge(\det A+\det B)/4$ is equivalent to
--
--   $$
--   4(ab-c_1^2)(ab-c_2^2)\ge a^2+b^2+2|c_1c_2|-\frac14.
--   $$
--
--   This is an exact algebraic specialization. It makes no assertion that arbitrary parameters describe a physical state.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, PDF p.4: explicit specialization of (19) to (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P92

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsSeparable IsBarycenter)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Advance50.P48
  (TwoKernel GaussianTwo IsDiscordCovariance characteristicTwo
   covarianceModeBlock totalPhotonEnergy)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase Covariance twoModeStandard)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel unitaryCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, unnumbered display following (19): exact standard-form specialization.
This is an algebraic equivalence, not an assertion of physicality of every V0. -/
theorem standardFormCriterion (a b c1 c2 : ℝ) :
    SimonCriterion (twoModeStandard a b c1 c2) ↔
      a ^ 2 + b ^ 2 + 2 * |c1 * c2| - 1 / 4 ≤
        4 * (a * b - c1 ^ 2) * (a * b - c2 ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
