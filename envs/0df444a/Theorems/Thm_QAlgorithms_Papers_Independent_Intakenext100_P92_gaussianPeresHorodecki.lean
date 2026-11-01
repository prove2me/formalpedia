-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_gaussianPeresHorodecki
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.gaussianPeresHorodecki
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:32:55.171096+00:00
-- url     : https://prove2.me/theorems/d4e601ef-6951-46a7-8dc7-5673c80ec596
-- title:
--   Two-mode Gaussian Peres–Horodecki separability criterion
-- statement:
--   Let $\rho$ be a positive trace-class density operator of trace one on the completed two-oscillator Hilbert space, with Alice owning one mode and Bob the other. Suppose $\rho$ is Gaussian, with arbitrary mean $d\in\mathbb R^4$ and covariance $V=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ in the order $(q_1,p_1,q_2,p_2)$, where $[q_j,p_k]=i\delta_{jk}$ and the vacuum covariance is $I_4/2$. Put $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, $\Omega=J\oplus J$, and $\Lambda=\operatorname{diag}(1,1,1,-1)$. Then
--
--   $$
--   \rho\text{ is separable}\quad\Longleftrightarrow\quad
--   \det A\det B+\left(\frac14-|\det C|\right)^2-\operatorname{tr}(AJCJBJC^TJ)\ge\frac{\det A+\det B}{4}.
--   $$
--
--   Equivalently, $\rho^{T_B}$ is a positive trace-one density operator, or $\Lambda V\Lambda+i\Omega/2\succeq0$. Here separability means the trace-norm closed convex hull of product densities. Pure Gaussian states and $\det C=0$ are included. This gives an invariant covariance test for separability on this one-mode versus one-mode cut.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 4, Theorem, PDF p.4 (announced p.1): two-mode Gaussian Peres–Horodecki criterion

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

/-- Theorem, PDF p.4, proof p.5: Simon (19) characterizes separability for
one oscillator versus one oscillator, including pure modes and det C=0. -/
theorem gaussianPeresHorodecki (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (hgauss : GaussianTwo rho d V) :
    (IsSeparable rho ↔ SimonCriterion V) ∧
    (IsSeparable rho ↔ IsDensity (bobTranspose rho)) ∧
    (IsSeparable rho ↔ IsDiscordCovariance (reflectedCovariance V)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
