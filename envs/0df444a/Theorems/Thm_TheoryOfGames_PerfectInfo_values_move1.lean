-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_values_move1
-- name    : TheoryOfGames.PerfectInfo.values_move1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T02:33:33.75827+00:00
-- url     : https://prove2.me/theorems/eb46f94a-ccfe-44f0-a749-36f466a10ece
-- title:
--   (15:4), (15:5) — $v_k = \operatorname{Max}_{\sigma_1} v_{\sigma_1/k}$ when the first move is player 1's
-- statement:
--   Let $\Gamma$ be a game tree whose first move $\mathfrak M_1$ is a personal move of player 1 with alternatives $\sigma_1 = 1, \dots, \alpha_1$ ($\alpha_1 \geqq 1$), followed by the games $\Gamma_{\sigma_1}$. With $v_1, v_2$ the quantities of $\Gamma$ and $v_{\sigma_1/1}, v_{\sigma_1/2}$ those of $\Gamma_{\sigma_1}$,
--   $$v_1 = \operatorname{Max}_{\sigma_1} v_{\sigma_1/1}, \qquad v_2 = \operatorname{Max}_{\sigma_1} v_{\sigma_1/2}.$$
--
--   No strict determinateness is assumed. This is the case $k_1 = 1$ of (15:8); the formula for $v_2$ is the step of the book's argument that rests on (13:E).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 120–122, 15.5.1, (15:4), (15:5)

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:4), (15:5): if the first move is a personal move of player 1, then
`v₁ = Max_{σ₁} v_{σ₁/1}` and `v₂ = Max_{σ₁} v_{σ₁/2}`. -/
theorem values_move1 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) :
    v1 (move1 α hα next) =
        Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v1 (next σ)) ∧
      v2 (move1 α hα next) =
        Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v2 (next σ)) := by sorry

end TheoryOfGames.PerfectInfo
