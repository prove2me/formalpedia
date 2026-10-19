-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_asymmetric_positions
-- name    : PPDifferentiation.ShortRun.asymmetric_positions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:12.923722+00:00
-- url     : https://prove2.me/theorems/501b5dcb-4fd8-4422-8a79-685df510b2be
-- title:
--   (3) — asymmetric positioning equilibrium
-- statement:
--   For $t>0$, suppose only A uses personalized pricing. A is the targeting follower and B is the uniform-price leader. The positioning subgame has an equilibrium at
--
--   $$x_A^{AS}=-\frac12,\qquad x_B^{AS}=\frac12.$$
--
--   The positioning comparison includes moves to every real point, including a move across the rival's location. It provides the positions used in the asymmetric implementation-payoff cells.
--
--   **Formalization Note** This is a weak equilibrium: A can move to the reflected position $3/2$ and tie its equilibrium gross profit. At coincident positions the leader may have multiple optimal prices, so the predicate chooses an optimal continuation after a deviation. The source optimizes over ordered locations; the statement checks the full real-location game.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 24, display (3)

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem asymmetric_positions (t : ℝ) (ht : 0 < t) :
    IsPosEqAS t (-1/2) (1/2) := by sorry

end PPDifferentiation.ShortRun
