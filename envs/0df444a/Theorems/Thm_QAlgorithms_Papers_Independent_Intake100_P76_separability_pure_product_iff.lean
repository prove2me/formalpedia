-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_separability_pure_product_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.separability_pure_product_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:21:31.43099+00:00
-- url     : https://prove2.me/theorems/2d0245d9-89b7-4f9c-92d8-9b41c79e21f5
-- title:
--   Separability as a finite mixture of pure product projectors
-- statement:
--   Let $H_A$ and $H_B$ be finite-dimensional nonzero complex Hilbert spaces, with $H_A$ the first tensor factor, and let $\rho$ be a positive semidefinite operator of trace one on $H_A\otimes H_B$. Separability, defined as a finite convex combination of tensor products of local density matrices, is equivalent to the existence of a finite number $m$, real weights $w_k$, and unit local vectors $e_k\in H_A$, $f_k\in H_B$, such that
--
--   $$\rho=\sum_{k=1}^{m}w_k|e_k\otimes f_k\rangle\langle e_k\otimes f_k|,\qquad 0\leq w_k\leq1,\qquad\sum_{k=1}^{m}w_k=1.$$
--
--   This identifies the pure product projectors used in separable subtraction with the mixed-product definition of separability.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 1, Eq. (2): pure product representation of separability

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.1, Eqs. (1)–(2): mixed-product separability is equivalent to a finite
convex combination of normalized pure product projectors. -/
theorem separability_pure_product_iff [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    IsSeparableDensity rho ↔
      ∃ m : ℕ, ∃ w : Fin m → ℝ,
        ∃ e : Fin m → EuclideanSpace ℂ A, ∃ f : Fin m → EuclideanSpace ℂ B,
          (∀ k, 0 ≤ w k ∧ w k ≤ 1) ∧ (∑ k, w k) = 1 ∧
          (∀ k, IsState (e k) ∧ IsState (f k)) ∧
          rho = ∑ k, (w k : ℂ) • pureDensity (tensorVec (e k) (f k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
