-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a24_regime_two_comparison
-- name    : SellVsPPU.Duopoly.a24_regime_two_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:44.342836+00:00
-- url     : https://prove2.me/theorems/4736e39a-e3ec-40a0-9cfe-371c8d99d970
-- title:
--   A.2.4, p. 42 — second-regime iso-profit equation and sign
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   In the regime $q_m(a/2-\delta)<c$, equality of the tabulated profits is equivalent to
--
--   $$
--   2aq_m(aq_m-c)^2=\bigl(q_m(a-\delta)-c\bigr)(aq_m+c)^2.
--   $$
--
--   The service provider earns at least as much as the seller exactly when
--
--   $$
--   \delta\le a-\frac{c}{q_m}-2a\left(\frac{aq_m-c}{aq_m+c}\right)^2.
--   $$
--
--   This supplies the second algebraic branch of Proposition 3's threshold. The sign comparison extends the paper's displayed equality calculation.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 42, A.2.4, second paragraph

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- The sign comparison is stronger than the printed iso-profit equality calculation. -/
theorem a24_regime_two_comparison (P : Params) (hP : P.Admissible)
    (hregime : P.qm * (P.a / 2 - P.delta) < P.c) :
    (profSStar P = profUStar P ↔
      2 * P.a * P.qm * (P.a * P.qm - P.c) ^ 2 =
        (P.qm * (P.a - P.delta) - P.c) * (P.a * P.qm + P.c) ^ 2) ∧
    (profSStar P ≤ profUStar P ↔
      P.delta ≤ P.a - P.c / P.qm -
        2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2) := by sorry

end SellVsPPU.Duopoly
