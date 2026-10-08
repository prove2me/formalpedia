-- Prove2me | Theorems.Thm_TensorNP_Rank_rankQ_tensorA_gt_two
-- name    : TensorNP.Rank.rankQ_tensorA_gt_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:40.305498+00:00
-- url     : https://prove2.me/theorems/6e8809dd-6f2a-4044-a695-401277f393a1
-- title:
--   Proof of Theorem 1.14, p. 0:26 — rank_ℚ(A) > 2 for the explicit tensor A
-- statement:
--   Let $\mathcal A = 2\mathbf x\otimes\mathbf x\otimes\mathbf x - 4\mathbf y\otimes\mathbf y\otimes\mathbf x + 4\mathbf y\otimes\mathbf x\otimes\mathbf y - 4\mathbf x\otimes\mathbf y\otimes\mathbf y \in \mathbb Q^{2\times2\times2}$ with $\mathbf x = [1,0]^\top$, $\mathbf y = [0,1]^\top$. Then
--   $$
--   \operatorname{rank}_{\mathbb Q}(\mathcal A) > 2 .
--   $$
--
--   Together with $\operatorname{rank}_{\mathbb R}(\mathcal A) \le 2$ this proves Theorem 1.14 for this explicit tensor.
--
--   **Formalization Note** The rank over $\mathbb Q$ allows only rational coefficients and vectors in the decomposition (6).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, proof of Theorem 1.14, last sentence

import Mathlib
import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction

namespace TensorNP.Rank

theorem rankQ_tensorA_gt_two : 2 < rankOver ℚ tensorA := by sorry

end TensorNP.Rank
