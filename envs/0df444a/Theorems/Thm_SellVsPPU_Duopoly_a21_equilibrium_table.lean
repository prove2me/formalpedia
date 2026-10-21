-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a21_equilibrium_table
-- name    : SellVsPPU.Duopoly.a21_equilibrium_table
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:32.419861+00:00
-- url     : https://prove2.me/theorems/95ad0861-d510-46b8-a165-bce56a7e1383
-- title:
--   A.2.1, p. 37 — tabulated prices form an equilibrium with the stated profits
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   The prices $p_s^*$ and $p_u^*$ in the Appendix A.2.1 table form a price equilibrium of the utility-defined duopoly. At that equilibrium the actual model profits equal the table's values:
--
--   $$
--   \Pi_s(p_s^*,p_u^*)=\Pi_s^*,\qquad
--   \Pi_u(p_s^*,p_u^*)=\Pi_u^*.
--   $$
--
--   For $c\le q_m(a/2-\delta)$, the prices are $(3c+2\delta q_m)/2$ and $2c_u$; otherwise they are $(c+aq_m)/2$ and $a$. The full profit formulas are given by the shared model definition.
--
--   **Formalization Note** Equilibrium here means global maximization of the integral-defined profits, a stronger claim than checking only the paper's first-order and KKT equations.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), pp. 36–37, A.2.1, equilibrium table

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- Stronger than the calculation on the page: the table prices satisfy global price-equilibrium inequalities for the integral-defined profits. -/
theorem a21_equilibrium_table (P : Params) (hP : P.Admissible) :
    IsPriceEq P (psStar P) (puStar P) ∧
    profitS P (psStar P) (puStar P) = profSStar P ∧
    profitU P (psStar P) (puStar P) = profUStar P := by sorry

end SellVsPPU.Duopoly
