-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_a21_equilibrium_profit_unique
-- name    : SellVsPPU.Duopoly.a21_equilibrium_profit_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:19.698285+00:00
-- url     : https://prove2.me/theorems/c28fd448-5624-4a0a-aa5f-d3fd4a1e7406
-- title:
--   A.2.1, pp. 36–37 — all price equilibria have the tabulated profits (stronger than printed)
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   Every price equilibrium of the asymmetric selling versus service subgame has the profit pair listed in Appendix A.2.1:
--
--   $$
--   \Pi_s(p_s,p_u)=\Pi_s^*,\qquad \Pi_u(p_s,p_u)=\Pi_u^*.
--   $$
--
--   This identifies the profits used in Proposition 3 independently of which equilibrium prices represent them.
--
--   **Formalization Note** The paper calls the table the overall solution but does not prove uniqueness. Price uniqueness would be false at $c=aq_m,\delta=0$: several seller prices yield the same zero profits. This statement asserts exactly the profit uniqueness needed for the goal.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), pp. 36–37, A.2.1, final paragraph and equilibrium table

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

/-- Stronger than printed: the paper calls its table the overall solution but does not prove uniqueness. The theorem asserts unique profits, since prices are not unique at c = a*q_m and delta = 0. -/
theorem a21_equilibrium_profit_unique (P : Params) (hP : P.Admissible) :
    ∀ ps pu, IsPriceEq P ps pu →
      profitS P ps pu = profSStar P ∧ profitU P ps pu = profUStar P := by sorry

end SellVsPPU.Duopoly
