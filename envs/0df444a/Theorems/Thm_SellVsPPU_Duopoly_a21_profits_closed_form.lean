-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a21_profits_closed_form
-- name    : SellVsPPU.Duopoly.a21_profits_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:20.281843+00:00
-- url     : https://prove2.me/theorems/9257967f-6a07-40df-aed5-fbbf47b3b7c9
-- title:
--   A.2.1, (1)–(2), p. 36 — duopoly profit integrals in closed form
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   For seller price $p_s$ and service price $p_u$ with $0<p_u\le a$ and $0\le p_s\le q_m p_u$, the indifferent customer's usage is $\bar q=p_s/p_u\in[0,q_m]$. The model's profit integrals equal
--
--   $$
--   \Pi_s(p_s,p_u)=\frac{(p_s-c)(q_m-p_s/p_u)}{q_m},\qquad
--   \Pi_u(p_s,p_u)=\frac{p_s^2(p_u-c_u)}{2q_m p_u^2}.
--   $$
--
--   These formulas connect the utility-defined market segments to the algebraic calculations in Appendix A.2.1.
--
--   **Formalization Note** The price bounds make the displayed integration limits valid and every division by $p_u$ well defined.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 36, A.2.1, equations (1)–(2)

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

theorem a21_profits_closed_form (P : Params) (hP : P.Admissible)
    (ps pu : ℝ) (hpu : 0 < pu) (hpuA : pu ≤ P.a)
    (hps0 : 0 ≤ ps) (hpsq : ps ≤ P.qm * pu) :
    profitS P ps pu = (ps - P.c) * (P.qm - ps / pu) / P.qm ∧
    profitU P ps pu = ps ^ 2 * (pu - cu P) / (2 * P.qm * pu ^ 2) := by sorry

end SellVsPPU.Duopoly
