-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_simpleTensorsNumericalZero
-- name    : QAlgorithms.Papers.Independent.Information100.P75.simpleTensorsNumericalZero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:10:45.654066+00:00
-- url     : https://prove2.me/theorems/f9aca9f4-c6d9-450c-9db3-7ae6df5cb8d6
-- title:
--   Numerical-range zero for simple tensors and their span
-- statement:
--   Let $n,m\ge1$ and let $\mathcal A\subset M_n(\mathbb C)$, $\mathcal B\subset M_m(\mathbb C)$ be complex subspaces. Write $W(X)$ for the numerical range and $\mathcal A\otimes\mathcal B$ for the span of the simple tensors. Then
--
--   $$[\forall A\in\mathcal A\ \forall B\in\mathcal B:\ 0\in W(A\otimes B)]
--   \iff [\forall X\in\mathcal A\otimes\mathcal B:\ 0\in W(X)].$$
--
--   This upgrades a condition on simple tensors to the whole tensor subspace, without assuming a common density witness.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 5, Corollary 6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Corollary 6, PDF p.5: pointwise numerical-range zero for simple tensors iff
pointwise numerical-range zero for their entire complex linear span. -/
theorem simpleTensorsNumericalZero {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (M : Submodule ℂ (Mat ι)) (L : Submodule ℂ (Mat κ)) :
    (∀ X ∈ M, ∀ Y ∈ L, 0 ∈ numericalRange (Matrix.kronecker X Y)) ↔
    (∀ T ∈ tensorSpace M L, 0 ∈ numericalRange T) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
