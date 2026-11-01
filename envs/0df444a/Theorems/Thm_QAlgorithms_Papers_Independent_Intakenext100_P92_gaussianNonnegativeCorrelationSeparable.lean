-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_gaussianNonnegativeCorrelationSeparable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.gaussianNonnegativeCorrelationSeparable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:41:33.712114+00:00
-- url     : https://prove2.me/theorems/8e7728a8-0cd5-4442-9daa-3e83a8c190fa
-- title:
--   Gaussian states with nonnegative correlation determinant are separable
-- statement:
--   Let $\rho$ be a normalized Gaussian density of two complete canonical oscillator modes, one per party, with arbitrary first moments and finite half-anticommutator covariance $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ in the order $(q_1,p_1,q_2,p_2)$ and units $\hbar=1$. Then
--
--   $$
--   \det C\ge0\quad\Longrightarrow\quad\rho\text{ is separable}.
--   $$
--
--   Separability means the trace-norm closed convex hull of product densities. Both $\det C>0$ and the entire boundary $\det C=0$, including pure product states, are covered. This lemma supplies the nonnegative-correlation case of the Gaussian criterion.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 5, Lemma, PDF p.5: Gaussian states with det C >= 0 are separable

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

/-- Lemma, PDF p.5: includes both det C>0 and det C=0 and all displacements.
Printed proof arithmetic: the scaled off-diagonal coefficient 2ab c1 should be
2 sqrt(ab) c1 for the displayed scaling. The lemma statement is unchanged;
this proof discrepancy is recorded for independent moderation. -/
theorem gaussianNonnegativeCorrelationSeparable (rho : TwoKernel) (d : (modePhase 2) → ℝ)
    (V : Covariance 2) (hgauss : GaussianTwo rho d V)
    (hC : 0 ≤ simonInvariant V 2) : IsSeparable rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
