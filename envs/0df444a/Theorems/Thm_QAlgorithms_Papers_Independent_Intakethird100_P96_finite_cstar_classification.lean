-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_finite_cstar_classification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.finite_cstar_classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:33:29.754942+00:00
-- url     : https://prove2.me/theorems/57028500-ab49-4665-ad37-55fb05a02481
-- title:
--   Finite-dimensional complex C*-algebras have unique matrix block sizes
-- statement:
--   Let $A$ be a finite-dimensional complex C*-algebra. There is a unique finite nonincreasing list of positive integers $n_1\ge\cdots\ge n_k\ge1$ for which
--
--   $$A\cong\bigoplus_{\mu=1}^k M_{n_\mu}(\mathbb C)$$
--
--   as complex star algebras. The empty list is allowed and represents the zero algebra. The isomorphism itself need not be unique.
--
--   The ordered list completely determines the algebra up to star isomorphism. A finite direct sum is represented by the componentwise finite product.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 18, Proposition 11: finite-dimensional C*-algebra classification

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

/-- Proposition 11, PDF p.18: unique ordered positive matrix sizes.
The empty list represents the zero algebra. Finite products are finite direct sums. -/
theorem finite_cstar_classification (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    ∃! sizes : List ℕ,
      (∀ n ∈ sizes, 0 < n) ∧ sizes.Pairwise (fun a b => b ≤ a) ∧
      Nonempty (A ≃⋆ₐ[ℂ] ((i : Fin sizes.length) → Mat (sizes.get i))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
