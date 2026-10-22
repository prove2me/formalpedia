-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_even_restriction
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_even_restriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:04:51.742259+00:00
-- url     : https://prove2.me/theorems/a5a73811-0771-4a12-a148-6c2580868cc1
-- title:
--   Proposition 1.13
-- statement:
--   For a nonzero real pseudo-Euclidean space, let $S$ be its full irreducible Clifford module and $C$ the even-action commutant. For each $K\in\{\mathbb R,\mathbb C,\mathbb H\}$, $C$ has simple $K$-matrix type, respectively split $K$-matrix type, if and only if the even Clifford algebra has the same type. Moreover,
--   $$\begin{aligned}S\text{ is even-irreducible}&\iff C\cong K\text{ for some }K,\\S\text{ is a sum of two equivalent even-irreducibles}&\iff C\cong\operatorname{Mat}_2(K)\text{ for some }K,\\S\text{ is a sum of two inequivalent even-irreducibles}&\iff C\cong K\oplus K\text{ for some }K.\end{aligned}$$
--   All isomorphisms are real algebra isomorphisms. Submodule equivalence means an invertible real linear intertwiner, and the sums are internal direct sums. This retains both directions of every classification clause.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 17, Proposition 1.13

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 1.13, PDF p. 17: retain every equivalence, including equivalent versus
inequivalent irreducible pairs. K ranges over R,C,H via the explicit alternatives. -/
theorem real_even_restriction (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S) :
    (∀ t : RealAlgebraType, HasRealAlgebraType (schurAlgebra rho) t ↔
      HasRealAlgebraType (RealEvenCl p q) t) ∧
    (IrreducibleOperators (evenOperators rho) ↔
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] ℝ) ∨ Nonempty (schurAlgebra rho ≃ₐ[ℝ] ℂ) ∨
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] Quaternion ℝ)) ∧
    (TwoIrreducibleSummands rho true ↔
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) ∨
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) ∨
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Quaternion ℝ))) ∧
    (TwoIrreducibleSummands rho false ↔
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] (ℝ × ℝ)) ∨
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] (ℂ × ℂ)) ∨
      Nonempty (schurAlgebra rho ≃ₐ[ℝ] (Quaternion ℝ × Quaternion ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
