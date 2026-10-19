-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_tensor_destroys_domination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.tensor_destroys_domination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:56:10.438667+00:00
-- url     : https://prove2.me/theorems/e708d8eb-b8f5-4639-801e-3a3b9601bf02
-- title:
--   Theorem 5.2: domination fails under tensor products
-- statement:
--   There exist channels $\Phi$ and $\Psi$ on positive finite-dimensional systems such that
--   $$\Phi\text{ and }\Psi\text{ each admit a dominating transmittable algebra},\qquad
--   \Phi\otimes\Psi\text{ admits none}.$$
--   Thus domination is not stable under tensor products. The cited joint protocol is used in the source proof, not assumed in this theorem.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 45, Theorem 5.2: domination fails under tensor products

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.45, Theorem 5.2: domination fails under tensor products. -/
theorem tensor_destroys_domination :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      ∃ F : Superop (Fin a) (Fin b), ∃ G : Superop (Fin c) (Fin d),
        IsChannel F ∧ IsChannel G ∧ HasDominating F ∧ HasDominating G ∧
          ¬ HasDominating (tensorChannel F G) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
