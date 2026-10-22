-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_rc_cost_add_agent_le
-- name    : StrategyproofMinimax.Circle.rc_cost_add_agent_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:23:47.113462+00:00
-- url     : https://prove2.me/theorems/d83af380-8432-4f78-8730-906c076acf75
-- title:
--   Lemma A.7 — adding an agent at y does not raise y's cost under RC
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are not on one semicircle, and let $y\in G$. Adding an agent located at $y$ to the profile does not increase the expected distance from $y$ under the random center mechanism:
--   $$\operatorname{cost}(\operatorname{rc}(x),y)\ge\operatorname{cost}(\operatorname{rc}(x\cup\{y\}),y).$$
--   Adding the agent inserts the antipodal point $\hat y$ as a new cut point, which splits one arc of the RC partition into two.
--
--   **Formalization Note.** $x\cup\{y\}$ is the profile with $n+1$ agents `Fin.snoc x y` (the new agent is last). If $y$ coincides with an existing agent, `rc` is unchanged and the inequality is an equality.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 522, Lemma A.7

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.7 (p. 522). If the agents are not on one semicircle, adding an agent at a point `y`
(the profile `x ∪ {y}`, here `Fin.snoc x y` with `n + 1` agents) does not raise the expected
cost of `y` under RC. -/
theorem rc_cost_add_agent_le {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (hx : ¬ OnSemicircle x)
    (y : AddCircle (1 : ℝ)) :
    cost (rc (Fin.snoc (α := fun _ => AddCircle (1 : ℝ)) x y)) y ≤ cost (rc x) y := by sorry

end StrategyproofMinimax.Circle
