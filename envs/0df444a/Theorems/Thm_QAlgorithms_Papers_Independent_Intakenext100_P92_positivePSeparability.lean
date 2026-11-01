-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P92_positivePSeparability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P92.positivePSeparability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:40:56.614288+00:00
-- url     : https://prove2.me/theorems/64883f16-c6b1-4c55-8db3-f7dc76b78977
-- title:
--   Positive-P states and their local canonical transforms are separable
-- statement:
--   Let $\rho$ be any normalized density on the completed two-oscillator space that admits a coherent-product representation by a Borel probability measure $\mu$ on $\mathbb C^2$:
--
--   $$
--   \rho=\int |z_1\rangle\langle z_1|\otimes|z_2\rangle\langle z_2|\,d\mu(z_1,z_2).
--   $$
--
--   Then $\rho$ is separable in the trace-norm closed convex hull of product densities. For every pair of zero-displacement local symplectic implementing unitaries $U_1,U_2$, the density $(U_1\otimes U_2)\rho(U_1\otimes U_2)^\dagger$ is separable as well. This applies to arbitrary, possibly singular positive P measures without Gaussianity or finite-energy assumptions.
-- source:
--   Peres-Horodecki separability criterion for continuous variable systems, arXiv:quant-ph/9909044v1, PDF p. 5, PDF pp.4–5: classical states and their local canonical transforms are separable

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

/-- PDF pp.4--5: positive-P states and all their local canonical transforms
are separable, with no Gaussian, energy, or finite-moment restriction. -/
theorem positivePSeparability (rho : TwoKernel) (hclass : IsClassicalTwo rho) :
    IsSeparable rho ∧
    ∀ U1 U2 : AffineMultimodeGaussianUnitary 1,
      U1.displacement = 0 → U2.displacement = 0 →
        IsSeparable (localStateAction U1 U2 rho) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P92

end
