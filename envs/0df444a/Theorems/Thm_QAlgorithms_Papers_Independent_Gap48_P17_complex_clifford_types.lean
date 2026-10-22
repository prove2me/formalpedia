-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_complex_clifford_types
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.complex_clifford_types
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:02:49.023412+00:00
-- url     : https://prove2.me/theorems/81fb77bb-636f-4e0a-9bef-4392078bb604
-- title:
--   Proposition 1.9
-- statement:
--   Let $V=\mathbb C^d$ with $d>0$ and its standard nondegenerate complex bilinear metric. Use the negative metric as the Clifford quadratic form. Its even/full complex algebra types are
--   $$t_d=\begin{cases}(2\mathbb C,\mathbb C),&d\text{ even},\\(\mathbb C,2\mathbb C),&d\text{ odd}.\end{cases}$$
--   As in the real case, a type means an algebra isomorphism to positive-size matrices, and $2\mathbb C$ means a product of two equal-size matrix algebras. The field of every algebra isomorphism here is $\mathbb C$.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 15, Proposition 1.9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Proposition 1.9, PDF p. 15: complex even/full Clifford types in positive dimension. -/
theorem complex_clifford_types (d : ℕ) (hd : 0 < d) :
    if Even d then
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexEvenCl d ≃ₐ[ℂ]
        (Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) (Fin k) ℂ))) ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexCl d ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ))
    else
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexEvenCl d ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)) ∧
      (∃ k : ℕ, 0 < k ∧ Nonempty (ComplexCl d ≃ₐ[ℂ]
        (Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) (Fin k) ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
