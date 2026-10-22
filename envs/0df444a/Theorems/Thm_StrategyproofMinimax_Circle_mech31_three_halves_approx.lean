-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_mech31_three_halves_approx
-- name    : StrategyproofMinimax.Circle.mech31_three_halves_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:39:15.1447+00:00
-- url     : https://prove2.me/theorems/a2b19a57-60a5-4749-9e98-ece893ceb8aa
-- title:
--   Lemma A.1 — Mechanism 3.1 is a 3/2-approximation for the minimax
-- statement:
--   On the circle $G$ of circumference one, Mechanism 3.1 is a $3/2$-approximation mechanism for the minimax: for every number $n$ of agents and every location profile $x\in G^n$,
--   $$\operatorname{mc}(\operatorname{mech31}(x),x)\le\tfrac32\cdot\min_{z\in G}\operatorname{mc}(\delta_z,x).$$
--   The expected maximum distance from the facility to an agent is at most $3/2$ times the smallest maximum distance any single facility location achieves. By the lower bound of Procaccia and Tennenholtz on the line, no strategyproof randomized mechanism has a smaller ratio.
--
--   **Formalization Note.** This is the second conjunct of the goal theorem (`IsApproximation (3/2)`); the inequality is multiplicative, so it is meaningful when the optimum is $0$ (all agents at one point).
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 519, Lemma A.1

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_mech31

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.1 (p. 519). Mechanism 3.1 is a `3/2`-approximation mechanism for the minimax. -/
theorem mech31_three_halves_approx :
    IsApproximation (3 / 2) (fun _ x => mech31 x) := by sorry

end StrategyproofMinimax.Circle
