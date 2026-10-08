-- Prove2me | Theorems.Thm_ShapleyScarf_Balanced_marketGame_isBalancedGame
-- name    : ShapleyScarf.Balanced.marketGame_isBalancedGame
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:42.282984+00:00
-- url     : https://prove2.me/theorems/55928b42-77a8-4b2f-893f-cbd71832e9be
-- title:
--   Section 4, Theorem — the housing market game is balanced
-- statement:
--   For every nonempty finite set of traders and every real preference matrix $A$, including matrices with ties, the housing market characteristic function $V$ is a balanced game. It satisfies the three defining conditions for a game without side payments and, for every balanced family $T$ of nonempty coalitions,
--   $$
--   \bigcap_{S\in T}V(S)\subseteq V(N).
--   $$
--
--   The paper continues, “hence the market in question has a nonempty core,” by invoking a separate general theorem that a balanced game has a nonempty core. This formal statement records the paper's proved classification of $V$; that cited external consequence is outside this mission.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; p. 110 of the source printing, Section 4, Theorem

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_BalancedGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem marketGame_isBalancedGame {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsBalancedGame (marketGame A) := by sorry

end ShapleyScarf.Balanced
