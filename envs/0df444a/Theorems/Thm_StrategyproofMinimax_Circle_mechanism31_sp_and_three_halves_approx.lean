-- Prove2me | Theorems.Thm_StrategyproofMinimax_Circle_mechanism31_sp_and_three_halves_approx
-- name    : StrategyproofMinimax.Circle.mechanism31_sp_and_three_halves_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T21:45:19.248677+00:00
-- url     : https://prove2.me/theorems/e528c26e-b9bc-45e5-9807-674e7bf84195
-- title:
--   Theorem 3.1 — Mechanism 3.1 is a strategyproof 3/2-approximation mechanism on the circle
-- statement:
--   Let $G$ be a circle, with the arc-length distance $d$. **Mechanism 3.1** runs the left-right-middle (LRM) mechanism on the covering semicircle when the agents are on one semicircle, and the random center (RC) mechanism otherwise. Then Mechanism 3.1 is
--
--   1. **strategyproof**: for every number $n$ of agents, every profile $x\in G^n$, every agent $i$ and every misreport $x_i'\in G$,
--   $$\operatorname{cost}(\operatorname{mech31}(x),x_i)\le\operatorname{cost}(\operatorname{mech31}(x_i',x_{-i}),x_i);$$
--   2. a **$3/2$-approximation mechanism for the minimax**: for every profile $x\in G^n$,
--   $$\operatorname{mc}(\operatorname{mech31}(x),x)\le\tfrac32\cdot\min_{z\in G}\operatorname{mc}(\delta_z,x).$$
--
--   Procaccia and Tennenholtz showed that no strategyproof randomized mechanism achieves a ratio below $3/2$ even on a line, so this is the best ratio possible on the circle. The deviation in the first part is arbitrary, and it may switch the mechanism between LRM and RC.
--
--   **Formalization Note.** The circle is normalized to circumference one (`AddCircle (1 : ℝ)`), as in the paper's Appendix A. Rescaling the circle multiplies every distance, every cost and every maximum cost by the same factor, so both strategyproofness and the ratio $3/2$ are invariant under the normalization. Mechanisms are families indexed by $n$; the deviated profile is `Function.update x i x'`. For agents occupying exactly one antipodal pair, `lrm` fixes one of the two covering semicircles (see the definition of `lrm`); the paper leaves this choice open.
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 517, Theorem 3.1

import Mathlib
import Definitions.Def_StrategyproofMinimax_Circle_cost
import Definitions.Def_StrategyproofMinimax_Circle_mech31

namespace StrategyproofMinimax.Circle

open MeasureTheory

/-- Theorem 3.1 (p. 517). On the circle, Mechanism 3.1 is strategyproof and a
`3/2`-approximation mechanism for the minimax. -/
theorem mechanism31_sp_and_three_halves_approx :
    IsStrategyproof (fun _ x => mech31 x) ∧ IsApproximation (3 / 2) (fun _ x => mech31 x) := by sorry

end StrategyproofMinimax.Circle
