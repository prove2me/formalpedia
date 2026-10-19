-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_uniform_positions
-- name    : PPDifferentiation.ShortRun.uniform_positions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:02.848482+00:00
-- url     : https://prove2.me/theorems/93f597fa-ace7-46e9-bc67-9daed15ef053
-- title:
--   §4 Stage 1 — benchmark positions, prices and profits
-- statement:
--   For $t>0$, when both firms use uniform pricing, the positioning subgame has an equilibrium at $x_A=-1/4$ and $x_B=5/4$. Each then charges $3t/2$ and earns gross profit
--
--   $$\pi_A=\pi_B=\frac{3t}{4}.$$
--
--   The position equilibrium compares each firm's profit with deviations to every real position and with price equilibria following those deviations. It supplies the no-PP cell of the implementation game.
--
--   **Formalization Note** The predicate quantifies over price equilibria after deviations, without asserting that one exists after every possible deviation. Reservation value is omitted because the covered-market assumption makes it cancel.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §4, p. 9, Stage 1

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem uniform_positions (t : ℝ) (ht : 0 < t) :
    IsPosEqUU t (-1/4) (5/4) (3*t/2) (3*t/2) ∧
    PPDifferentiation.Costless.uProf t (-1/4) (5/4) (3*t/2) (3*t/2) = 3*t/4 ∧
    PPDifferentiation.Costless.uProf t (5/4) (-1/4) (3*t/2) (3*t/2) = 3*t/4 := by sorry

end PPDifferentiation.ShortRun
