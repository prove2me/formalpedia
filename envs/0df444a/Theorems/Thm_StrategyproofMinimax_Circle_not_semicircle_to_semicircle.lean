-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_not_semicircle_to_semicircle
-- name    : StrategyproofMinimax.Circle.not_semicircle_to_semicircle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:14:39.575821+00:00
-- url     : https://prove2.me/theorems/e57a488f-179b-4bf7-bcaa-ea2a83e0b242
-- title:
--   Lemma A.6 (Not Semicircle to Semicircle) — a deviation from RC to LRM does not pay
-- statement:
--   Let $x\in G^n$ be a location profile on the circle $G$ of circumference one whose agents are not on one semicircle, and let agent $i$ deviate to $x_i'$ so that in the new profile $x'=(x_i',x_{-i})$ the agents are on one semicircle. Then
--   $$\operatorname{cost}(\operatorname{rc}(x),x_i)\le\operatorname{cost}(\operatorname{lrm}(x'),x_i).$$
--   A deviation that switches Mechanism 3.1 from the random center mechanism to LRM does not lower the deviating agent's expected cost.
--
--   **Formalization Note.** $x'$ is `Function.update x i x'`; the hypotheses are `¬ OnSemicircle x` and `OnSemicircle x'`.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 522, Lemma A.6

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_lrm
import Definitions.Def_StrategyproofMinimax_Circle_rc

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Lemma A.6 (Not Semicircle to Semicircle, p. 522). If the agents are not on one semicircle,
and after agent `i` deviates they are, the deviation does not lower `i`'s expected cost. -/
theorem not_semicircle_to_semicircle {n : ℕ} (x : Fin n → AddCircle (1 : ℝ)) (i : Fin n)
    (x' : AddCircle (1 : ℝ)) (hx : ¬ OnSemicircle x)
    (hx' : OnSemicircle (Function.update x i x')) :
    cost (rc x) (x i) ≤ cost (lrm (Function.update x i x')) (x i) := by sorry

end StrategyproofMinimax.Circle
