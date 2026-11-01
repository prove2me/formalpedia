-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_gaussianClassicality
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.gaussianClassicality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:40:13.821748+00:00
-- url     : https://prove2.me/theorems/de95797a-818f-4c32-a58e-b340cf1cbf64
-- title:
--   Gaussian positive-P classicality including the boundary
-- statement:
--   Let $\rho$ be a normalized two-mode Gaussian density on the completed oscillator space, with arbitrary first moments and half-anticommutator covariance $V$ in units $\hbar=1$. Classicality means that there is a Borel probability measure $\mu$ on $\mathbb C^2$ with $\rho=\int |z_1\rangle\langle z_1|\otimes|z_2\rangle\langle z_2|\,d\mu(z_1,z_2)$, where $|z\rangle$ is the normalized coherent vector. Then
--
--   $$
--   \rho\text{ is classical}\quad\Longleftrightarrow\quad V-\tfrac12 I_4\succeq0.
--   $$
--
--   The measure may be singular, so vacuum, coherent states, and zero excess-noise directions are included. This characterizes positive generalized P representations without requiring a smooth density.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 5, PDF p.5: Gaussian positive-P classicality criterion

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

/-- PDF pp.4--5: Gaussian positive-P classicality, including singular probability
measures and the vacuum boundary V-I/2=0. All first moments are allowed. -/
theorem gaussianClassicality (rho : TwoKernel) (d : (modePhase 2) → ℝ) (V : Covariance 2)
    (hgauss : GaussianTwo rho d V) :
    IsClassicalTwo rho ↔ (V - (1 / 2 : ℝ) • (1 : Covariance 2)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
