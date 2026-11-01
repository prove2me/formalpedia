-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_second_order_full
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.second_order_full
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:41:50.405158+00:00
-- url     : https://prove2.me/theorems/1d3b1832-2e04-4e9a-a334-ece19b64912a
-- title:
--   Full second-order equivariant layers
-- statement:
--   Let $n\ge1$, and let $L$ be a real linear endomorphism of all real $n\times n$ matrices, with simultaneous inverse permutation of both indices. Fix any shared pointwise nonlinearity $\xi$. Write $F_{i*}=\sum_k F_{ik}$, $F_{*i}=\sum_kF_{ki}$, $F_{**}=\sum_{k,l}F_{kl}$, and $\operatorname{tr}F=\sum_kF_{kk}$. Then $L$ is equivariant if and only if weights $w_0,\ldots,w_{14}\in\mathbb R$ exist, independently of the input, with
--
--   $$
--   \begin{aligned}
--   (LF)_{ij}={}&w_0F_{ij}+w_1F_{ji}+w_2F_{i*}+w_3F_{*i}+w_4F_{*j}+w_5F_{j*}+w_6F_{**}\\
--   &+w_7\operatorname{tr}F+w_8F_{ii}+w_9F_{jj}\\
--   &+\delta_{ij}\bigl(w_{10}F_{ii}+w_{11}\operatorname{tr}F+w_{12}F_{**}+w_{13}F_{i*}+w_{14}F_{*i}\bigr).
--   \end{aligned}
--   $$
--
--   The layer applies $\xi$ to this expression. The diagonal coordinates are present and unrestricted, including zero values. The formula spans the linear layers even in small dimensions, where coefficients may be redundant.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 5, Corollary 4 (§4): full second order layer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Corollary 4, source PDF p.5 (proof p.15). The entire matrix space is used;
“non-zero diagonal” means present, unconstrained diagonal coordinates. -/
theorem second_order_full (n : ℕ) (hn : 1 ≤ n) (xi : ℝ → ℝ)
    (L : Tensor n 2 →ₗ[ℝ] Tensor n 2) :
    (L ∈ equivariantLinearMaps (permutationTensorAction (n := n) (k := 2)) permutationTensorAction ↔
      ∃ w : Fin 15 → ℝ, ∀ F i j, L F ![i,j] = fifteenFormula w F i j) ∧
    (L ∈ equivariantLinearMaps (permutationTensorAction (n := n) (k := 2)) permutationTensorAction →
      ∃ w : Fin 15 → ℝ, ∀ F i j,
        pointwise xi (L F) ![i,j] = xi (fifteenFormula w F i j)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
