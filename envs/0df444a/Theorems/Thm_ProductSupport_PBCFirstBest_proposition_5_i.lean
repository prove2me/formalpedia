-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_proposition_5_i
-- name    : ProductSupport.PBCFirstBest.proposition_5_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:59.874212+00:00
-- url     : https://prove2.me/theorems/130407c9-f99f-49a9-b2f9-a7113b309546
-- title:
--   Proposition 5(i) — first-best PBC menu is optimal under condition (10)
-- statement:
--   Suppose the two-type product-support model satisfies its standing assumptions and condition (10):
--   $$
--   \frac{\mu_H^0-\lambda_L}{\mu_H^0-\lambda_H}
--   \leq\frac{M_L}{M_H}
--   \leq\frac{\mu_L^0-\lambda_L}{\mu_L^0-\lambda_H}.
--   $$
--   If both first-best uptime prices $v_L^0,v_H^0$ are strictly positive, then the first-best menu is feasible and maximizes the supplier's expected payoff among all feasible PBC menus. Both customer participation constraints bind exactly, so each customer's information rent is zero. The contracts separate the types because $\mu_L^0<\mu_H^0$.
--
--   This is the first region of Proposition 5's screening result: information asymmetry leaves the first-best PBC allocation attainable.
--
--   **Formalization Note** Strict positivity of both first-best prices is an explicit added hypothesis because problem (9) requires $v_\tau>0$. The standing predicate also records $M_H>0$, $M_L>M_H$, and $\lambda_L<\lambda_H$; condition (10) then gives nonzero denominators for the first-best prices and ratios.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), p. 18 (PDF 18), Proposition 5(i), condition (10); supplement p. 9 (PDF 42), proof of Proposition 5(i)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem proposition_5_i (P : Params) (hS : P.Standing) (h10 : Cond10 P)
    (hvL : 0 < v0 P P.lamL P.ML) (hvH : 0 < v0 P P.lamH P.MH) :
    (fbMenu P).Feasible P ∧
    (∀ m : Menu, m.Feasible P →
      objective P m ≤ objective P (fbMenu P)) ∧
    custPayoff P P.lamL (fbMenu P).L = P.ML ∧
    custPayoff P P.lamH (fbMenu P).H = P.MH ∧
    (fbMenu P).L.mu < (fbMenu P).H.mu := by sorry

end ProductSupport.PBCFirstBest
