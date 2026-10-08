-- Prove2me | Theorems.Thm_ShapleyScarf_Balanced_marketGame_isNTUGame
-- name    : ShapleyScarf.Balanced.marketGame_isNTUGame
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:16.664146+00:00
-- url     : https://prove2.me/theorems/088ff582-299f-4416-94ec-f17439e586cf
-- title:
--   Section 4 — the housing market satisfies game conditions (a)–(c)
-- statement:
--   In a nonempty finite housing market with arbitrary real preference matrix $A$, including ties, the characteristic function $V$ defined by feasible coalition permutations is a game without side payments. For every nonempty coalition $S$, $V(S)$ is closed and downward closed in the payoff coordinates of $S$, and
--   $$
--   \bigl[V(S)\setminus\bigcup_{i\in S}\operatorname{int}V(\{i\})\bigr]\cap E^S
--   $$
--   is bounded and nonempty.
--
--   This records the three regularity conditions the paper states immediately before proving balance. The coordinate slice $E^S$ sets coordinates outside $S$ to zero.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; p. 110 of the source printing, Section 4, proof of the Theorem, first sentence

import Mathlib
import Definitions.Def_ShapleyScarf_Balanced_NTUGame
import Definitions.Def_ShapleyScarf_Balanced_MarketGame

namespace ShapleyScarf.Balanced

theorem marketGame_isNTUGame {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (A : N → N → ℝ) : IsNTUGame (marketGame A) := by sorry

end ShapleyScarf.Balanced
