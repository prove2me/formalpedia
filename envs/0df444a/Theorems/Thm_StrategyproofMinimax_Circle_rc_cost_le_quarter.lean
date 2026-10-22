-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_rc_cost_le_quarter
-- name    : StrategyproofMinimax.Circle.rc_cost_le_quarter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:04:53.207098+00:00
-- url     : https://prove2.me/theorems/76ab674f-c8e2-4f5c-8e03-8b77e055c47a
-- title:
--   Lemma A.5 — under RC every agent's expected cost is at most 1/4
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are **not** on one semicircle. Then under the random center mechanism every agent's expected distance to the facility is at most a quarter of the circumference:
--   $$\operatorname{cost}(\operatorname{rc}(x),x_i)\le\tfrac14\qquad\text{for all } i\in N .$$
--   The bound is the value a uniformly random facility would give; it is the pivot of the two deviation cases in which the mechanism switches between RC and LRM.
--
--   **Formalization Note.** "Not on one semicircle" is `¬ OnSemicircle x`; `rc` is the finite weighted sum of Dirac masses defined in this mission.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 521, Lemma A.5

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.5 (p. 521). If the agents are not on one semicircle, every agent's expected cost
under RC is at most `1/4`. -/
theorem rc_cost_le_quarter {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (hx : ¬ OnSemicircle x)
    (i : Fin n) :
    cost (rc x) (x i) ≤ 1 / 4 := by sorry

end StrategyproofMinimax.Circle
