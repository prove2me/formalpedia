-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_mirrorInvariants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.mirrorInvariants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:37:37.350019+00:00
-- url     : https://prove2.me/theorems/a79eac00-f345-40b0-b9d9-5d8ce2941607
-- title:
--   Partial reflection flips the correlation determinant
-- statement:
--   Let $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be a real symmetric two-mode covariance array. Put $Z=\operatorname{diag}(1,-1)$, $\Lambda=I_2\oplus Z$, $\widetilde V=\Lambda V\Lambda$, and define $I_1=\det A$, $I_2=\det B$, $I_3=\det C$, $I_4=\operatorname{tr}(AJCJBJC^TJ)$ with $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Then
--
--   $$
--   \widetilde A=A,\quad\widetilde B=ZBZ,\quad\widetilde C=CZ,\qquad
--   \widetilde I_1=I_1,\quad\widetilde I_2=I_2,\quad\widetilde I_3=-I_3,\quad\widetilde I_4=I_4.
--   $$
--
--   Also $\det\widetilde V=\det V$, and the scalar inequality $I_1I_2+(1/4-|I_3|)^2-I_4\ge(I_1+I_2)/4$ holds for $\widetilde V$ exactly when it holds for $V$. No physicality of the reflected array is assumed; these are algebraic reflection identities.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, PDF p.4 after (18): partial reflection flips det C and preserves the other invariants

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

/-- PDF p.4 after (18): reflection acts on the blocks and flips only I3.
The reflected covariance need not be the covariance of a positive density. -/
theorem mirrorInvariants (V : Covariance 2) (hsymm : V.IsSymm) :
    covarianceModeBlock (reflectedCovariance V) 0 0 = covarianceModeBlock V 0 0 ∧
    covarianceModeBlock (reflectedCovariance V) 1 1 =
      localReflection * covarianceModeBlock V 1 1 * localReflection ∧
    covarianceModeBlock (reflectedCovariance V) 0 1 =
      covarianceModeBlock V 0 1 * localReflection ∧
    simonInvariant (reflectedCovariance V) 0 = simonInvariant V 0 ∧
    simonInvariant (reflectedCovariance V) 1 = simonInvariant V 1 ∧
    simonInvariant (reflectedCovariance V) 2 = -simonInvariant V 2 ∧
    simonInvariant (reflectedCovariance V) 3 = simonInvariant V 3 ∧
    (reflectedCovariance V).det = V.det ∧
    (SimonCriterion (reflectedCovariance V) ↔ SimonCriterion V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
