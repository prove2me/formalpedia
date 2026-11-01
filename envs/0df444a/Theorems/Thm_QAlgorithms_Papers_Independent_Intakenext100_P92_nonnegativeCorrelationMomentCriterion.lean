-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_nonnegativeCorrelationMomentCriterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.nonnegativeCorrelationMomentCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:39:05.513758+00:00
-- url     : https://prove2.me/theorems/b5990891-63b3-4d22-b3bc-728ee58f24d7
-- title:
--   Nonnegative correlation determinant passes the moment test
-- statement:
--   Let $\rho$ be any normalized two-mode oscillator density with finite first and second moments and covariance $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$, in interleaved coordinates with vacuum covariance $I_4/2$. If $\det C\ge0$, then, for $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$,
--
--   $$
--   \det A\det B+(1/4-|\det C|)^2-\operatorname{tr}(AJCJBJC^TJ)\ge\frac{\det A+\det B}{4}.
--   $$
--
--   Gaussianity is unnecessary for this automatic second-moment test. This conclusion alone does not assert separability of a non-Gaussian state.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, PDF p.4: nonnegative correlation determinant automatically passes the moment test

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

/-- PDF p.4: every actual finite covariance with det C>=0 satisfies (19).
This moment assertion does not require Gaussianity and does not assert separability. -/
theorem nonnegativeCorrelationMomentCriterion (rho : TwoKernel) (d : (modePhase 2) → ℝ)
    (V : Covariance 2) (hmom : TwoModeMoments rho d V)
    (hC : 0 ≤ simonInvariant V 2) : SimonCriterion V := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
