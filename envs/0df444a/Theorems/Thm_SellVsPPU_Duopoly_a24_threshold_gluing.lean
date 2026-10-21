-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a24_threshold_gluing
-- name    : SellVsPPU.Duopoly.a24_threshold_gluing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:30.674876+00:00
-- url     : https://prove2.me/theorems/c2d04192-577e-46d1-adfb-4f7ed53696ff
-- title:
--   A.2.4, p. 42 — glue the two regime comparisons at the threshold (stronger than printed)
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   The regime-specific profit comparisons both agree with the piecewise threshold $\bar\delta(c)$ of Proposition 3. In the first price regime, $\delta\le c/(2q_m)$ is equivalent to $\delta\le\bar\delta(c)$. In the second regime, the bound $\delta\le a-c/q_m-2a((aq_m-c)/(aq_m+c))^2$ is equivalent to the same threshold inequality:
--
--   $$
--   \Pi_s^*\le\Pi_u^*\iff\delta\le\bar\delta(c)
--   \quad\text{in either regime}.
--   $$
--
--   The theorem reconciles the price-regime boundary with the different boundary $c=aq_m/3$ in the proposition's threshold.
--
--   **Formalization Note** The page states only the meeting value $\delta=a/6$ at $c=aq_m/3$; this full equivalence is an additional bridge needed for the goal.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 42, A.2.4, first and second paragraphs; p. 14, Proposition 3

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- Stronger than printed: p. 42 states the meeting value at c = a*q_m/3; this theorem reconciles both full regime comparisons with Proposition 3. -/
theorem a24_threshold_gluing (P : Params) (hP : P.Admissible) :
    (P.c ≤ P.qm * (P.a / 2 - P.delta) →
      (P.delta ≤ P.c / (2 * P.qm) ↔ P.delta ≤ deltaBar P.a P.qm P.c)) ∧
    (P.qm * (P.a / 2 - P.delta) < P.c →
      (P.delta ≤ P.a - P.c / P.qm -
        2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2 ↔
        P.delta ≤ deltaBar P.a P.qm P.c)) := by sorry

end SellVsPPU.Duopoly
