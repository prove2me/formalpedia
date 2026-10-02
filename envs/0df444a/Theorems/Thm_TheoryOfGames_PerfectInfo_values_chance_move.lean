-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_values_chance_move
-- name    : TheoryOfGames.PerfectInfo.values_chance_move
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T02:31:07.529827+00:00
-- url     : https://prove2.me/theorems/5c768d32-2bf5-4c89-8312-2f40b263c3cc
-- title:
--   (15:2), (15:3) — $v_k = \sum_{\sigma_1} p_1(\sigma_1) v_{\sigma_1/k}$ when the first move is a chance move
-- statement:
--   Let $\Gamma$ be a game tree whose first move $\mathfrak M_1$ is a chance move with alternatives $\sigma_1 = 1, \dots, \alpha_1$ of probabilities $p_1(\sigma_1) \geqq 0$, $\sum_{\sigma_1} p_1(\sigma_1) = 1$, followed by the games $\Gamma_{\sigma_1}$. Write $v_1, v_2$ for the quantities of $\Gamma$ and $v_{\sigma_1/1}, v_{\sigma_1/2}$ for those of $\Gamma_{\sigma_1}$. Then
--   $$v_1 = \sum_{\sigma_1=1}^{\alpha_1} p_1(\sigma_1)\, v_{\sigma_1/1}, \qquad v_2 = \sum_{\sigma_1=1}^{\alpha_1} p_1(\sigma_1)\, v_{\sigma_1/2}.$$
--
--   Nothing is assumed about strict determinateness of $\Gamma$ or the $\Gamma_{\sigma_1}$: the max-min and the min-max of the normalized form each satisfy the recursion separately. This is the case $k_1 = 0$ of the inductive step (15:8).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 118–119, 15.4.2, (15:2), (15:3)

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:2), (15:3): if the first move is a chance move with probabilities `p₁(σ₁)`, then
`v₁ = ∑ p₁(σ₁) v_{σ₁/1}` and `v₂ = ∑ p₁(σ₁) v_{σ₁/2}`. -/
theorem values_chance_move (α : ℕ) (p : Fin α → ℝ) (next : Fin α → GameTree)
    (hp : ∀ σ, 0 ≤ p σ) (hsum : ∑ σ, p σ = 1) :
    v1 (chance α p next hp hsum) = ∑ σ, p σ * v1 (next σ) ∧
      v2 (chance α p next hp hsum) = ∑ σ, p σ * v2 (next σ) := by sorry

end TheoryOfGames.PerfectInfo
