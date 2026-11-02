-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P77_gaussian_rotation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P77.gaussian_rotation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:11:49.872638+00:00
-- url     : https://prove2.me/theorems/71498bc0-8e41-4584-8625-9a6682af173a
-- title:
--   Quadratic Gaussian conjugation and all special orthogonal rotations
-- statement:
--   Let $c_1,\ldots,c_{2n}$ be Hermitian operators on the full $n$-qubit Hilbert space with $c_\mu c_\nu+c_\nu c_\mu=2\delta_{\mu\nu}I$. For a real antisymmetric matrix $h$, set $H=i\sum_{\mu\ne\nu}h_{\mu\nu}c_\mu c_\nu$ and $U=e^{iH}$. Then
--
--   $$Uc_\mu U^\dagger=\sum_\nu(e^{4h})_{\mu\nu}c_\nu,\qquad U^\dagger c_\mu U=\sum_\nu(e^{-4h})_{\mu\nu}c_\nu.$$
--
--   Both real coefficient matrices are orthogonal with determinant one, and every matrix in $SO(2n)$ is $e^{4h}$ for such an $h$ and hence is induced by this conjugation. Both ordered off-diagonal terms are included and scalar Hamiltonian terms are omitted. This is the rotation interface underlying the simulation results.
--
--   **Source correction.** The printed displayed theorem puts $e^{4h}$ beside the opposite adjoint action. The statement follows the convention and differential equation in the source proof.
-- source:
--   Matchgates and classical simulation of quantum circuits, arXiv:0804.4050v2, PDF p. 9, Theorem 3: Gaussian conjugation induces every special orthogonal rotation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P77

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P77

open QAlgorithms

open QAlgorithms.Complexity (Str)

open QAlgorithms.Papers.Independent.Advance50.P19 (Major CARSystem)

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9 Theorem 3, corrected using its own proof: exp(4h) describes
U c U†, while exp(-4h) describes U† c U. The literal displayed theorem has the
adjoint sign reversed. Surjectivity is included, including the n=0 case. -/
theorem gaussian_rotation {n : ℕ} (c : CARSystem n) :
    (∀ h : Matrix (Major n) (Major n) ℝ, Skew h →
      IsMajoranaRotation (NormedSpace.exp ((4 : ℝ) • h)) ∧
      IsMajoranaRotation (NormedSpace.exp ((-4 : ℝ) • h)) ∧
      (∀ i, gaussianOperation c.majorana h * c.majorana i * star (gaussianOperation c.majorana h) =
        ∑ j, ((NormedSpace.exp ((4 : ℝ) • h)) i j : ℂ) • c.majorana j) ∧
      (∀ i, star (gaussianOperation c.majorana h) * c.majorana i * gaussianOperation c.majorana h =
        ∑ j, ((NormedSpace.exp ((-4 : ℝ) • h)) i j : ℂ) • c.majorana j)) ∧
    (∀ R : Matrix (Major n) (Major n) ℝ, IsMajoranaRotation R →
      ∃ h : Matrix (Major n) (Major n) ℝ, Skew h ∧
        NormedSpace.exp ((4 : ℝ) • h) = R ∧
        ∀ i, gaussianOperation c.majorana h * c.majorana i * star (gaussianOperation c.majorana h) =
          ∑ j, (R i j : ℂ) • c.majorana j) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P77

end
