-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_semicircle_to_not_semicircle
-- name    : StrategyproofMinimax.Circle.semicircle_to_not_semicircle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:28:51.180814+00:00
-- url     : https://prove2.me/theorems/ff7c9fbb-7b69-4868-9bb5-6803ec93d5e8
-- title:
--   Lemma A.8 (Semicircle to Not Semicircle) — a deviation from LRM to RC does not pay
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are on one semicircle, and let agent $i$ deviate to $x_i'$ so that in the new profile $x'=(x_i',x_{-i})$ the agents are not on one semicircle. Then
--   $$\operatorname{cost}(\operatorname{lrm}(x),x_i)\le\operatorname{cost}(\operatorname{rc}(x'),x_i).$$
--   A deviation that switches Mechanism 3.1 from LRM to the random center mechanism does not lower the deviating agent's expected cost.
--
--   **Formalization Note.** $x'$ is `Function.update x i x'`; the hypotheses are `OnSemicircle x` and `¬ OnSemicircle x'`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 522, Lemma A.8

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.8 (Semicircle to Not Semicircle, p. 522). If the agents are on one semicircle, and
after agent `i` deviates they are not, the deviation does not lower `i`'s expected cost. -/
theorem semicircle_to_not_semicircle {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (i : Fin n)
    (x' : AddCircle (1 : ℝ)) (hx : OnSemicircle x)
    (hx' : ¬ OnSemicircle (Function.update x i x')) :
    cost (lrm x) (x i) ≤ cost (rc (Function.update x i x')) (x i) := by sorry

end StrategyproofMinimax.Circle
