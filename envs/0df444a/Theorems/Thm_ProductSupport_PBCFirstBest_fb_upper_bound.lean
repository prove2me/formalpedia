-- Prove2me | Theorems.Thm_ProductSupport_PBCFirstBest_fb_upper_bound
-- name    : ProductSupport.PBCFirstBest.fb_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:56.16805+00:00
-- url     : https://prove2.me/theorems/7919aca2-7109-49e7-9607-38fddd987524
-- title:
--   Proof of Proposition 5(i) — first-best upper bound for every feasible PBC menu
-- statement:
--   For any feasible two-contract PBC screening menu, the supplier's prior-weighted objective satisfies
--   $$
--   \pi_s^P\leq\beta(\Pi_L^0-M_L)+(1-\beta)(\Pi_H^0-M_H).
--   $$
--   Feasibility includes positive terms, both participation constraints, and both incentive-compatibility constraints. This bound compares every admissible screening menu with the two full-information profit benchmarks and is the optimality step in the proof of Proposition 5(i).
--
--   **Formalization Note** The bound ranges over all feasible menus, including those with slack IR constraints; it does not presuppose the first-best form.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), supplement p. 9 (PDF 42), proof of Proposition 5(i), final paragraph of case (i)

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

namespace ProductSupport.PBCFirstBest

theorem fb_upper_bound (P : Params) (hS : P.Standing) (m : Menu)
    (hm : m.Feasible P) :
    objective P m ≤
      P.β * (Pi0 P P.lamL - P.ML) +
      (1 - P.β) * (Pi0 P P.lamH - P.MH) := by sorry

end ProductSupport.PBCFirstBest
