-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_strictly_determined_value
-- name    : TheoryOfGames.PerfectInfo.strictly_determined_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T02:58:06.297405+00:00
-- url     : https://prove2.me/theorems/0488898f-c577-4db2-94c8-f0d0dfad876c
-- title:
--   15.6.1 with (15:12) — every game with perfect information is strictly determined, with value given by (15:12)
-- statement:
--   Let $\Gamma$ be a finite zero-sum two-person game with perfect information, possibly containing chance moves, with normalized form $\mathcal H(\tau_1, \tau_2)$ over the pure strategies $\tau_1$, $\tau_2$ of the two players. Then $\Gamma$ is strictly determined, and its value is the backward-induction value of (15:12):
--   $$v_1 = \operatorname{Max}_{\tau_1} \operatorname{Min}_{\tau_2} \mathcal H(\tau_1, \tau_2) \;=\; v_2 = \operatorname{Min}_{\tau_2} \operatorname{Max}_{\tau_1} \mathcal H(\tau_1, \tau_2) \;=\; v = M^{k_1}_{\sigma_1} M^{k_2(\sigma_1)}_{\sigma_2} \cdots M^{k_\nu(\sigma_1, \dots, \sigma_{\nu-1})}_{\sigma_\nu} \mathfrak F_1(\pi(\sigma_1, \dots, \sigma_\nu)),$$
--   where $M^{k}_{\sigma}$ is the expectation $\sum_\sigma p(\sigma)\,\cdot$ at a chance move, $\operatorname{Max}_\sigma$ at a personal move of player 1 and $\operatorname{Min}_\sigma$ at a personal move of player 2 (15:8).
--
--   In words: the pure-strategy max-min and min-max of the normalized form coincide, so the game has a saddle point in pure strategies, and the common value is computed by backward induction over the game tree. The book stresses (15.7.1) that this holds also when the game contains chance moves (Backgammon as well as Chess).
--
--   **Formalization Note** The game is a finite game tree (see the game-tree definition): perfect information holds by construction, and plays may have different lengths, which contains the book's games of fixed length $\nu$. Both equalities $v_1 = v$ and $v_2 = v$ are asserted.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 123–124, 15.6.1, 15.6.2, (15:12)

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values
import Definitions.Def_TheoryOfGames_PerfectInfo_backwardValue

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- 15.6.1 with (15:12): every zero-sum two-person game with perfect information (chance moves
allowed) is strictly determined, `v₁ = v₂`, and its value is given by the formula (15:12),
`v₁ = v₂ = v = M^{k₁}_{σ₁} M^{k₂(σ₁)}_{σ₂} ⋯ M^{k_ν(σ₁,…,σ_{ν-1})}_{σ_ν} 𝔉₁(π(σ₁, …, σ_ν))`. -/
theorem strictly_determined_value (t : GameTree) :
    v1 t = backwardValue t ∧ v2 t = backwardValue t := by sorry

end TheoryOfGames.PerfectInfo
