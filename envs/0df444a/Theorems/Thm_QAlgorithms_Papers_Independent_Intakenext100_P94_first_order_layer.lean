-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_first_order_layer
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.first_order_layer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:40:29.396896+00:00
-- url     : https://prove2.me/theorems/d5cb18ee-e026-404f-a380-61433a72e633
-- title:
--   First-order permutation-equivariant linear layers
-- statement:
--   Let $n\ge1$, let $\xi:\mathbb R\to\mathbb R$ be the fixed shared pointwise nonlinearity, and let $L:\mathbb R^n\to\mathbb R^n$ be linear. Permutations act by $(\sigma f)_i=f_{\sigma^{-1}(i)}$. Then $L$ is equivariant if and only if there are real weights $w_0,w_1$, chosen independently of the input, such that
--
--   $$
--   (Lf)_i=w_0f_i+w_1\sum_{j=1}^n f_j\qquad\text{for every }f,i.
--   $$
--
--   Consequently the layer output is $f_i^{\rm out}=\xi(w_0f_i+w_1\sum_jf_j)$. This gives the complete linear layer form; at $n=1$ the coefficients are redundant. The paper credits this result to Zaheer et al. (2017).
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 4, Theorem 1 (§3): first order layer

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 1, source PDF p.4 (proof p.13), restating Zaheer et al. (2017).
The weights describe the linear map before a possibly noninjective xi; n=1 is allowed. -/
theorem first_order_layer (n : ℕ) (hn : 1 ≤ n) (xi : ℝ → ℝ)
    (L : Tensor n 1 →ₗ[ℝ] Tensor n 1) :
    (L ∈ equivariantLinearMaps (permutationTensorAction (n := n) (k := 1)) permutationTensorAction ↔
      ∃ w0 w1 : ℝ, ∀ F i, L F ![i] = w0 * F ![i] + w1 * ∑ j, F ![j]) ∧
    (L ∈ equivariantLinearMaps (permutationTensorAction (n := n) (k := 1)) permutationTensorAction →
      ∃ w0 w1 : ℝ, ∀ F i,
        pointwise xi (L F) ![i] = xi (w0 * F ![i] + w1 * ∑ j, F ![j])) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
