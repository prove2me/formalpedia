-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_maxMin_le_minMax
-- name    : TheoryOfGames.Minimax.maxMin_le_minMax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:10:57.14099+00:00
-- url     : https://prove2.me/theorems/15f5180e-0fcf-4cd7-8078-8bf7d8d71d4d
-- title:
--   (13:A*) — $\operatorname{Max}_x \operatorname{Min}_y \phi \le \operatorname{Min}_y \operatorname{Max}_x \phi$
-- statement:
--   Let $\phi(x, y)$ be a real-valued function on $X \times Y$ for which the maxima and minima of (13:4) exist (the standing hypothesis of 13.2.1). Then always
--   $$\operatorname{Max}_x \operatorname{Min}_y \phi(x, y) \le \operatorname{Min}_y \operatorname{Max}_x \phi(x, y).$$
--
--   This is the general form of the observation (13:A) on the three matrices of Figs. 12–14; in the game setting it says that the minorant game is never more favourable to player 1 than the majorant game.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 95, (13:A*)

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_SaddlePoint

namespace TheoryOfGames.Minimax

/-- (13:A*), p. 95: for every function `φ(x, y)` for which the maxima and minima of (13:4)
exist (13.2.1), `Max_x Min_y φ(x, y) ≤ Min_y Max_x φ(x, y)`. -/
theorem maxMin_le_minMax {X Y : Type*} (φ : X → Y → ℝ) (hφ : MaxMinAttained φ) :
    maxMin φ ≤ minMax φ := by sorry

end TheoryOfGames.Minimax
