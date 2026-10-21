-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a24_regime_one_comparison
-- name    : SellVsPPU.Duopoly.a24_regime_one_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:28.349484+00:00
-- url     : https://prove2.me/theorems/b54998c5-bd14-48a3-8839-53f3f2ac7c6b
-- title:
--   A.2.4, p. 42 — first-regime iso-profit equation and sign
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   In the regime $c\le q_m(a/2-\delta)$, equality of the tabulated profits is equivalent to the paper's factored equation. The sign of the comparison is determined by $\delta\le c/(2q_m)$:
--
--   $$
--   \Pi_s^*=\Pi_u^*\iff(5c+6\delta q_m)(c-2\delta q_m)=0,
--   \qquad
--   \Pi_s^*\le\Pi_u^*\iff\delta\le\frac{c}{2q_m}.
--   $$
--
--   On the iso-profit branch $c=2\delta q_m$, the regime condition implies $\delta\le a/6$. This is the first branch of the threshold calculation.
--
--   **Formalization Note** The sign equivalence is the global comparison needed by Proposition 3; the printed derivation explicitly gives the equality condition and iso-profit branch.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 42, A.2.4, first paragraph

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- The sign comparison is stronger than the printed iso-profit equality calculation. -/
theorem a24_regime_one_comparison (P : Params) (hP : P.Admissible)
    (hregime : P.c ≤ P.qm * (P.a / 2 - P.delta)) :
    (profSStar P = profUStar P ↔
      (5 * P.c + 6 * P.delta * P.qm) * (P.c - 2 * P.delta * P.qm) = 0) ∧
    (profSStar P ≤ profUStar P ↔ P.delta ≤ P.c / (2 * P.qm)) ∧
    (P.c = 2 * P.delta * P.qm → P.delta ≤ P.a / 6) := by sorry

end SellVsPPU.Duopoly
