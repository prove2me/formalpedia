-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_second_order_zero_diagonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.second_order_zero_diagonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:41:08.958671+00:00
-- url     : https://prove2.me/theorems/2dd12381-e1ad-45b9-ac30-ed53e26afcbf
-- title:
--   Second-order layers on ordered distinct pairs
-- statement:
--   Let $n\ge2$. Let $L$ be a real linear endomorphism of zero-diagonal $n\times n$ matrices, with the simultaneous inverse permutation action on both indices, and fix a shared pointwise nonlinearity $\xi:\mathbb R\to\mathbb R$. No symmetry of the matrices is assumed. Write $F_{i*}=\sum_kF_{ik}$, $F_{*i}=\sum_kF_{ki}$ and $F_{**}=\sum_{k,l}F_{kl}$. Then $L$ is equivariant if and only if there are weights $w_0,\ldots,w_6\in\mathbb R$ such that, for all inputs and all $i\ne j$,
--
--   $$
--   (LF)_{ij}=w_0F_{ij}+w_1F_{ji}+w_2F_{i*}+w_3F_{*i}+w_4F_{*j}+w_5F_{j*}+w_6F_{**}.
--   $$
--
--   The nonlinear layer applies $\xi$ to this expression on the ordered distinct-pair coordinates. This characterizes the linear map; independence of the seven weights is not claimed for $n=2,3$.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 4, Theorem 2 (§3): second order layer with zero diagonal

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 2, source PDF p.4 and pp.13–14. Output indices are distinct,
as in the proof. Ordered pairs, without symmetry; no independence claim for n<4. -/
theorem second_order_zero_diagonal (n : ℕ) (hn : 2 ≤ n) (xi : ℝ → ℝ)
    (L : DistinctSpace n 2 →ₗ[ℝ] DistinctSpace n 2) :
    (L ∈ equivariantLinearMaps (distinctAction (n := n) (k := 2)) distinctAction ↔
      ∃ w : Fin 7 → ℝ, ∀ F i j, i ≠ j →
        (L F).val ![i,j] = sevenFormula w F.val i j) ∧
    (L ∈ equivariantLinearMaps (distinctAction (n := n) (k := 2)) distinctAction →
      ∃ w : Fin 7 → ℝ, ∀ F i j, i ≠ j →
        xi ((L F).val ![i,j]) = xi (sevenFormula w F.val i j)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
