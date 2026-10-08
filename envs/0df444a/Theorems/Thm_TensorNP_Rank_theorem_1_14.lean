-- Prove2me | Theorems.Thm_TensorNP_Rank_theorem_1_14
-- name    : TensorNP.Rank.theorem_1_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:49.650984+00:00
-- url     : https://prove2.me/theorems/42b47b56-a0c6-485a-97e3-7953539b4c53
-- title:
--   Theorem 1.14 — there is a rational tensor A ∈ ℚ^{2×2×2} with rank_ℝ(A) < rank_ℚ(A)
-- statement:
--   Tensor rank depends on the field. There is a tensor $\mathcal A \in \mathbb Q^{2\times2\times2}$ with rational entries such that
--   $$
--   \operatorname{rank}_{\mathbb R}(\mathcal A) < \operatorname{rank}_{\mathbb Q}(\mathcal A),
--   $$
--   where $\operatorname{rank}_E$ is the rank (6) computed with coefficients and vectors from the field $E$.
--
--   For matrices the rank does not change when the field is enlarged; this theorem shows that for 3-tensors it can, even between $\mathbb Q$ and $\mathbb R$. In particular Håstad's NP-hardness of tensor rank over $\mathbb Q$ does not transfer to $\mathbb R$ automatically.
--
--   **Formalization Note** The existential is the printed statement. The milestones of this mission concern the paper's explicit tensor $2\mathbf x\otimes\mathbf x\otimes\mathbf x - 4\mathbf y\otimes\mathbf y\otimes\mathbf x + 4\mathbf y\otimes\mathbf x\otimes\mathbf y - 4\mathbf x\otimes\mathbf y\otimes\mathbf y$, for which $\operatorname{rank}_{\mathbb R} \le 2 < \operatorname{rank}_{\mathbb Q}$. The real rank is the rank of $\mathcal A$ with its entries cast to $\mathbb R$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:11, Theorem 1.14 (proof p. 0:26)

import Mathlib
import Definitions.Def_TensorNP_Rank_Defs

namespace TensorNP.Rank

theorem theorem_1_14 :
    ∃ A : Fin 2 → Fin 2 → Fin 2 → ℚ,
      rankOver ℝ (fun i j k => (A i j k : ℝ)) < rankOver ℚ A := by sorry

end TensorNP.Rank
