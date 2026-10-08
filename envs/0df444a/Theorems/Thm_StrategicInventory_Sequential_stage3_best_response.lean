-- Prove2me | Theorems.Thm_StrategicInventory_Sequential_stage3_best_response
-- name    : StrategicInventory.Sequential.stage3_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T04:50:50.880225+00:00
-- url     : https://prove2.me/theorems/20e71cf2-9c88-4be8-81a5-04df89f30ef8
-- title:
--   §3.1.1 — in equilibrium the supplier sells $q_s = (\alpha - q_2 - s)^+/2$ directly
-- statement:
--   Consider the sequential two-period game with demand intercept $\alpha > 0$, holding cost $h \ge 0$ and direct selling cost $s \ge 0$. Let $\sigma$ be any subgame perfect equilibrium. Take any feasible history $(w_1, Q_1, q_1, w_2, Q_2, q_2)$ up to the supplier's last move: $w_1, w_2 \ge 0$, $0 \le q_1 \le Q_1$, $Q_2 \ge 0$ and $0 \le q_2 \le (Q_1 - q_1) + Q_2$. At that history the supplier's direct selling quantity is
--
--   $$
--   q_s = \frac{(\alpha - q_2 - s)^+}{2}, \qquad x^+ = \max\{0, x\}.
--   $$
--
--   This is the last-stage best response on which the whole backward induction rests. It determines when the supplier's direct channel is active (when $q_2 < \alpha - s$) and how much the buyer's period-2 sales crowd it out.
--
--   **Formalization Note.** The paper states the formula at $q_2 = q_b(w)$, the buyer's period-2 quantity when it holds no inventory. The statement here holds at every feasible history, with or without inventory.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, p. 540, §3.1.1

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE

namespace StrategicInventory.Sequential

/-- §3.1.1, p. 540: in every subgame perfect equilibrium, at every feasible
history the supplier's direct selling quantity is `qs = (α − q2 − s)⁺ / 2`. -/
theorem stage3_best_response (α h s : ℝ) (hα : 0 < α) (hh : 0 ≤ h) (hs : 0 ≤ s)
    (σ : Profile) (hσ : IsSPE α h s σ)
    (w1 Q1 q1 w2 Q2 q2 : ℝ) (hw1 : 0 ≤ w1) (hq1 : 0 ≤ q1) (hq1Q1 : q1 ≤ Q1)
    (hw2 : 0 ≤ w2) (hQ2 : 0 ≤ Q2) (hq2 : 0 ≤ q2) (hq2I : q2 ≤ (Q1 - q1) + Q2) :
    σ.direct w1 Q1 q1 w2 Q2 q2 = max (α - q2 - s) 0 / 2 := by sorry

end StrategicInventory.Sequential
