-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_not_semicircle_to_not_semicircle
-- name    : StrategyproofMinimax.Circle.not_semicircle_to_not_semicircle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:34:52.999699+00:00
-- url     : https://prove2.me/theorems/7058c027-2516-457a-b37b-df0bf8601c7e
-- title:
--   Lemma A.9 (Not Semicircle to Not Semicircle) — RC deviations that keep RC do not pay
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are not on one semicircle, and let agent $i$ deviate to $x_i'$ so that in the new profile $x'=(x_i',x_{-i})$ the agents are still not on one semicircle. Then
--   $$\operatorname{cost}(\operatorname{rc}(x),x_i)\le\operatorname{cost}(\operatorname{rc}(x'),x_i).$$
--   Within the regime where Mechanism 3.1 runs the random center mechanism, no unilateral deviation lowers the deviating agent's expected cost.
--
--   **Formalization Note.** $x'$ is `Function.update x i x'`; the hypotheses are `¬ OnSemicircle x` and `¬ OnSemicircle x'`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 524, Lemma A.9

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.9 (Not Semicircle to Not Semicircle, p. 524). If the agents are not on one
semicircle before and after agent `i` deviates, the deviation does not lower `i`'s expected
cost under RC. -/
theorem not_semicircle_to_not_semicircle {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (i : Fin n)
    (x' : AddCircle (1 : ℝ)) (hx : ¬ OnSemicircle x)
    (hx' : ¬ OnSemicircle (Function.update x i x')) :
    cost (rc x) (x i) ≤ cost (rc (Function.update x i x')) (x i) := by sorry

end StrategyproofMinimax.Circle
