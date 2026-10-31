-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_gaussian_energy_conservation
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.gaussian_energy_conservation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:16:25.911748+00:00
-- url     : https://prove2.me/theorems/c785c3da-0275-462d-aa7f-101e51d607f9
-- title:
--   §3.3 — conservation constraint on Gaussian fluctuations
-- statement:
--   Assume detailed balance, positivity improvement, and Gibbs reservoir densities at positive inverse temperatures $\beta_j$ for one self-adjoint Hamiltonian. Let $D=\nabla^2e(0)$ and $\mu_D$ be the associated centered Gaussian. Then
--
--   $$\mu_D\{s\in\mathbb R^M:\beta^{-1}\cdot s\ne0\}=0.$$
--
--   Equivalently, its support lies on the closed energy-conservation hyperplane. No time reversal or nonsingularity of $D$ is required; a one-reservoir Gaussian can be $\delta_0$. This gives the Gaussian form of energy conservation.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 9, §3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.9: thermal conservation constrains the possibly singular Gaussian without TR. -/
theorem gaussian_energy_conservation {d M : ℕ} (D : DBData d M) (hER : ER D)
    (H : Mat d) (beta : EntropyCoordinates M) (hThermal : Thermal D H beta) :
    (coordinateHessianAtZero (entropySpectralCGF D)).PosSemidef ∧
    centeredGaussianLaw (coordinateHessianAtZero (entropySpectralCGF D)) {s : EntropyCoordinates M | reservoirPairing (fun j => (beta j)⁻¹) s ≠ 0} = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
