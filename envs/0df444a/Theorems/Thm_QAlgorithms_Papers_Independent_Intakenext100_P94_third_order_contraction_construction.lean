-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_third_order_contraction_construction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.third_order_contraction_construction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:45:44.035452+00:00
-- url     : https://prove2.me/theorems/29cc8b37-d60a-4111-9e34-3ea2e6f98b04
-- title:
--   The specified contraction construction spans third-order linear layers
-- statement:
--   Let $n\ge6$ and consider real linear maps on full order-three tensors, equivariant for simultaneous inverse permutation of all indices. Form contractions by identifying any subset of the three input indices into blocks, retaining any subset of those blocks as free indices, and summing each remaining block once. Blocks are canonically named by their least input slot. There are respectively $1,6,10,5$ contractions of ranks $3,2,1,0$.
--
--   For generic output entries, inject the retained indices into the three output slots in every possible way. Add the analogous terms on each of the three equal-pair output supports, using two output slots, and on the all-equal support, using one slot. These are additions to the generic formula, so they also operate on intersections of the supports. If $K_p(t,u)$ is the resulting explicitly defined equality-constraint kernel, the weighted map is
--
--   $$
--   (\Phi_w F)(t)=\sum_p w_p\sum_u K_p(t,u)F(u).
--   $$
--
--   There are $77$ generic, $37$ terms for each of the three pair supports, and $15$ all-diagonal terms. Every equivariant linear map has a unique such weight vector:
--
--   $$
--   L\text{ is equivariant}\quad\Longleftrightarrow\quad\exists!w\in\mathbb R^{203},\ \forall F,\ L(F)=\Phi_w(F),\qquad77+3\cdot37+15=203.
--   $$
--
--   This states the paper’s contraction construction itself as a complete linear parametrization.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 16, §10.2 (Appendix C): contraction construction spans the third order layer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Appendix C §10.2, source PDF pp.15–16: the specified contraction algorithm
spans the equivariant linear layers and has 203 independent weights for n≥6.
Corrects “three” all-diagonal scalar contractions to one (p.16, item 4c) and
uses the stated two-index sum in item 3a. No closed formula is invented. -/
theorem third_order_contraction_construction (n : ℕ) (hn : 6 ≤ n) :
    (∀ r : Fin 4,
      Fintype.card {p : Recipe // p.val.2.card = r.val} = (![5,10,6,1] : Fin 4 → ℕ) r) ∧
    Fintype.card (PlacedRecipe 3) = 77 ∧
    Fintype.card (PlacedRecipe 2) = 37 ∧
    Fintype.card (PlacedRecipe 1) = 15 ∧
    Fintype.card ThirdIndex = 203 ∧
    (∀ L : Tensor n 3 →ₗ[ℝ] Tensor n 3,
      L ∈ equivariantLinearMaps (permutationTensorAction (n := n) (k := 3)) permutationTensorAction ↔
        ∃! w : ThirdIndex → ℝ, ∀ F, L F = thirdFormula w F) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
