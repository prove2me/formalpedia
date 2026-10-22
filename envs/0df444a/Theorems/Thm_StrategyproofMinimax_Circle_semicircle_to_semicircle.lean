-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_semicircle_to_semicircle
-- name    : StrategyproofMinimax.Circle.semicircle_to_semicircle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:58:54.991528+00:00
-- url     : https://prove2.me/theorems/c58265bd-fbe0-43ad-88e7-44d48e4c467e
-- title:
--   Lemma A.2 (Semicircle to Semicircle) — LRM deviations inside one semicircle do not pay
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are on one semicircle, and let agent $i$ deviate to $x_i'\in G$ so that in the new profile $x'=(x_i',x_{-i})$ the agents are again on one semicircle. Then agent $i$'s expected cost, measured from its true location $x_i$, does not decrease:
--   $$\operatorname{cost}(\operatorname{lrm}(x),x_i)\le\operatorname{cost}(\operatorname{lrm}(x'),x_i).$$
--   This is the first of the four deviation cases in the proof that Mechanism 3.1 is strategyproof. It does not follow from the strategyproofness of LRM on a line, because the deviation may move the covering semicircle.
--
--   **Formalization Note.** $x'$ is `Function.update x i x'`; "on one semicircle" is `OnSemicircle`; `lrm` includes a fixed tie-break for profiles occupying exactly one antipodal pair (see the definition).
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 519, Lemma A.2

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.2 (Semicircle to Semicircle, p. 519). If the agents are on one semicircle before and
after agent `i` deviates, the deviation does not lower `i`'s expected cost under LRM. -/
theorem semicircle_to_semicircle {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (i : Fin n)
    (x' : AddCircle (1 : ℝ)) (hx : OnSemicircle x)
    (hx' : OnSemicircle (Function.update x i x')) :
    cost (lrm x) (x i) ≤ cost (lrm (Function.update x i x')) (x i) := by sorry

end StrategyproofMinimax.Circle
