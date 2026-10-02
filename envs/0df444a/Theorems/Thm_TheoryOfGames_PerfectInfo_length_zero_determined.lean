-- Prove2me | Theorems.Thm_TheoryOfGames_PerfectInfo_length_zero_determined
-- name    : TheoryOfGames.PerfectInfo.length_zero_determined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T02:47:03.188492+00:00
-- url     : https://prove2.me/theorems/cbb46c94-ea70-4800-8773-9fb66b6685a6
-- title:
--   (15:C:a) — a game of length $\nu = 0$ is strictly determined with value $w$
-- statement:
--   Let $\Gamma$ be a game of length $\nu = 0$: it has no moves at all and pays the fixed amount $w$ to player 1 and $-w$ to player 2. Then each player has exactly one strategy, $\mathcal H(\tau_1, \tau_2) = w$, and
--   $$v_1 = v_2 = w,$$
--   so $\Gamma$ is strictly determined and its value is $w$.
--
--   This is the base case of the complete induction on the length $\nu$ in 15.6.1.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 123, 15.6.1, (15:C:a) and its proof

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

namespace TheoryOfGames.PerfectInfo

open GameTree

/-- (15:C:a): a game of length `ν = 0`, which pays the fixed amount `w` to player 1, is strictly
determined with `v₁ = v₂ = w`. -/
theorem length_zero_determined (w : ℝ) :
    v1 (leaf w) = w ∧ v2 (leaf w) = w := by sorry

end TheoryOfGames.PerfectInfo
