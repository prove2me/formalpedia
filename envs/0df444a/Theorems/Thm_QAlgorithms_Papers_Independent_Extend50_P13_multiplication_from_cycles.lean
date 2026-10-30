-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_multiplication_from_cycles
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.multiplication_from_cycles
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:33:53.394166+00:00
-- url     : https://prove2.me/theorems/e2898b62-7afe-443a-9d26-918b1ca4f233
-- title:
--   Proposition 2: matrix multiplication from cycles
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $k\ge3$, let $X_1,\ldots,X_k$ be arbitrary matrices and put $c=(1\,2\,\cdots\,k)$. With $\operatorname{tr}_{\ne q}$ retaining only slot $q$,
--
--   $$\operatorname{tr}_{\ne k}[T(c^{-1})(X_1\otimes\cdots\otimes X_k)]=X_1\cdots X_k,\qquad
--   \operatorname{tr}_{\ne1}[T(c)(X_1\otimes\cdots\otimes X_k)]=X_k\cdots X_1.$$
--
--   Here $T(\pi)$ moves an object at slot $i$ to slot $\pi(i)$. These formulas fix both multiplication order and partial-trace placement.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 8, Proposition 2: matrix multiplication from cycles

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Proposition 2, Eq.25 (PDF p.8). Both retained slots and both ordered products
are included, with the source's explicit k ≥ 3 restriction. -/
theorem multiplication_from_cycles {d k : ℕ} (hd : 0 < d) (hk : 3 ≤ k)
    (X : Fin k → (Matrix (Fin d) (Fin d) ℂ)) :
    let c := (List.finRange k).formPerm
    partialTraceSlot (⟨k-1, by omega⟩ : Fin k)
      (QAlgorithms.Schur.tensorPermutation d k c⁻¹ * tensorMatrices X) = (List.ofFn X).prod ∧
    partialTraceSlot (⟨0, by omega⟩ : Fin k)
      (QAlgorithms.Schur.tensorPermutation d k c * tensorMatrices X) = (List.ofFn X).reverse.prod := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
