-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_complex_even_restriction
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.complex_even_restriction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:05:40.594503+00:00
-- url     : https://prove2.me/theorems/45daf31b-b572-460a-9d78-ba5b55a6de71
-- title:
--   Proposition 1.14
-- statement:
--   Let $d>0$ and let $S$ be a full irreducible complex Clifford module for the standard complex bilinear metric on $\mathbb C^d$. If $d$ is even, then
--   $$S=S^+\oplus S^-$$
--   with two inequivalent irreducible even-Clifford submodules; both the even Clifford algebra and the complex Schur algebra are products of two isomorphic simple complex matrix algebras. If $d$ is odd, the even Clifford algebra is simple, $S$ is irreducible under its action, and the complex Schur algebra is simple. This records both module structure and algebra structure in each parity case.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 17, Proposition 1.14

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 1.14, PDF p. 17: both parity cases and both algebra conclusions. -/
theorem complex_even_restriction (d : ℕ) (hd : 0 < d)
    (S : Type*) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    if Even d then
      TwoIrreducibleSummands rho false ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexEvenCl d ≃ₐ[ℂ]
        (Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) (Fin k) ℂ))) ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (schurAlgebra rho ≃ₐ[ℂ]
        (Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) (Fin k) ℂ)))
    else
      IrreducibleOperators (evenOperators rho) ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexEvenCl d ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)) ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (schurAlgebra rho ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
