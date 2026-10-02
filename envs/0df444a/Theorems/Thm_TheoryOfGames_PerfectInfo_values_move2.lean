-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_values_move2
-- name    : TheoryOfGames.PerfectInfo.values_move2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T02:40:11.453001+00:00
-- url     : https://prove2.me/theorems/4f737380-5983-4f65-99cc-b31e70197653
-- title:
--   (15:6), (15:7) — $v_k = \operatorname{Min}_{\sigma_1} v_{\sigma_1/k}$ when the first move is player 2's
-- statement:
--   Let $\Gamma$ be a game tree whose first move $\mathfrak M_1$ is a personal move of player 2 with alternatives $\sigma_1 = 1, \dots, \alpha_1$ ($\alpha_1 \geqq 1$), followed by the games $\Gamma_{\sigma_1}$. With $v_1, v_2$ the quantities of $\Gamma$ and $v_{\sigma_1/1}, v_{\sigma_1/2}$ those of $\Gamma_{\sigma_1}$,
--   $$v_1 = \operatorname{Min}_{\sigma_1} v_{\sigma_1/1}, \qquad v_2 = \operatorname{Min}_{\sigma_1} v_{\sigma_1/2}.$$
--
--   No strict determinateness is assumed. This is the case $k_1 = 2$ of (15:8), obtained in 15.5.2 by interchanging the players.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 122, 15.5.2, (15:6), (15:7)

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:6), (15:7): if the first move is a personal move of player 2, then
`v₁ = Min_{σ₁} v_{σ₁/1}` and `v₂ = Min_{σ₁} v_{σ₁/2}`. -/
theorem values_move2 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) :
    v1 (move2 α hα next) =
        Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v1 (next σ)) ∧
      v2 (move2 α hα next) =
        Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v2 (next σ)) := by sorry

end TheoryOfGames.PerfectInfo
