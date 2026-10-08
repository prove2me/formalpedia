-- Prove2me | Theorems.Thm_TensorNP_Rank_real_decomposition
-- name    : TensorNP.Rank.real_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:43.896118+00:00
-- url     : https://prove2.me/theorems/d78da198-4776-42fa-8ad9-a479ef89df59
-- title:
--   Proof of Theorem 1.14, p. 0:26 — z̄⊗z⊗z̄ + z⊗z̄⊗z = A with z = x + √2 y, so rank_ℝ(A) ≤ 2
-- statement:
--   Let $\mathbf x = [1,0]^\top$, $\mathbf y = [0,1]^\top$, regarded in $\mathbb R^2$, and put $\mathbf z = \mathbf x + \sqrt2\,\mathbf y$ and $\bar{\mathbf z} = \mathbf x - \sqrt2\,\mathbf y$. Let $\mathcal A \in \mathbb Q^{2\times2\times2}$ be the tensor $2\mathbf x\otimes\mathbf x\otimes\mathbf x - 4\mathbf y\otimes\mathbf y\otimes\mathbf x + 4\mathbf y\otimes\mathbf x\otimes\mathbf y - 4\mathbf x\otimes\mathbf y\otimes\mathbf y$. Then
--   $$
--   \bar{\mathbf z}\otimes\mathbf z\otimes\bar{\mathbf z} + \mathbf z\otimes\bar{\mathbf z}\otimes\mathbf z = \mathcal A,
--   $$
--   and consequently $\operatorname{rank}_{\mathbb R}(\mathcal A) \le 2$.
--
--   This is the upper half of Theorem 1.14: over the reals, $\mathcal A$ is a sum of two outer products.
--
--   **Formalization Note** The identity is an equality of real $2\times2\times2$ arrays, with $\mathcal A$'s rational entries cast to $\mathbb R$; the rank bound is about the same cast tensor.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, proof of Theorem 1.14, first display

import Mathlib
import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction

namespace TensorNP.Rank

theorem real_decomposition :
    let x : Fin 2 → ℝ := fun i => (vecX i : ℝ)
    let y : Fin 2 → ℝ := fun i => (vecY i : ℝ)
    let z : Fin 2 → ℝ := x + Real.sqrt 2 • y
    let zbar : Fin 2 → ℝ := x - Real.sqrt 2 • y
    (outer zbar z zbar + outer z zbar z = fun i j k => (tensorA i j k : ℝ)) ∧
      rankOver ℝ (fun i j k => (tensorA i j k : ℝ)) ≤ 2 := by sorry

end TensorNP.Rank
