-- Prove2me | Theorems.Thm_SellVsPPU_Duopoly_proposition_3
-- name    : SellVsPPU.Duopoly.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:40.26847+00:00
-- url     : https://prove2.me/theorems/9d4bd40f-3a12-4425-b336-b62b81bd0dc7
-- title:
--   Proposition 3, p. 14 — service profit exceeds selling iff delivery cost is below the threshold
-- statement:
--   Let $a>0$ be value per use, $q_m>0$ the maximum usage, $c>0$ the product cost, and $\delta\ge0$ the delivery cost per use. Assume the service cost $c_u=c/q_m+\delta$ does not exceed $a$.
--
--   The asymmetric selling versus service price subgame has an equilibrium. At every such equilibrium, the service provider earns at least as much as the seller exactly when the delivery cost is no more than the explicit threshold $\bar\delta(c)$:
--
--   $$
--   \Pi_s(p_s,p_u)\le\Pi_u(p_s,p_u)
--   \quad\Longleftrightarrow\quad
--   \delta\le\bar\delta(c),
--   \qquad
--   \bar\delta(c)=
--   \begin{cases}
--    c/(2q_m),&c\le aq_m/3,\\
--    a-c/q_m-2a\bigl((aq_m-c)/(aq_m+c)\bigr)^2,&c>aq_m/3.
--   \end{cases}
--   $$
--
--   Thus delivery costs above the threshold give the seller strictly greater profit. The theorem characterizes the relative earnings of the two business models in the paper's asymmetric duopoly.
--
--   **Formalization Note** The paper compares equilibrium profits over admissible parameters. The theorem explicitly assumes $c_u\le a$, $c>0$, $\delta\ge0$, $a>0$, and $q_m>0$, asserts equilibrium existence, and evaluates the model's integral-defined profits at every global price equilibrium. The printed range $0\le c\le aq_m$ includes $c=0$; the model's standing assumption $c>0$ (§2.1, p. 7) excludes it, and $c\le aq_m$ follows from $c_u\le a$.
-- source:
--   Ladas, Kavadias & Loch, Product Selling vs. Pay-Per-Use Service, SSRN 3356458 manuscript (PDF of 16 Apr 2021; Management Science, doi:10.1287/mnsc.2021.4125), p. 14, Proposition 3

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.Duopoly

theorem proposition_3 (P : Params) (hP : P.Admissible) :
    (∃ ps pu, IsPriceEq P ps pu) ∧
    ∀ ps pu, IsPriceEq P ps pu →
      (profitS P ps pu ≤ profitU P ps pu ↔
        P.delta ≤ deltaBar P.a P.qm P.c) := by sorry

end SellVsPPU.Duopoly
