-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_route_isQRoute
-- name    : RobustBCPCVRP.Formulation.route_isQRoute
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:10.92198+00:00
-- url     : https://prove2.me/theorems/fedbc0f7-96b5-4825-8ed0-a6fea0d90ae8
-- title:
--   §1, p. 2 — every CVRP route is a q-route without 2-cycles
-- statement:
--   In a CVRP instance with graph $G=(V,E)$, demands $d$ and capacity $C$, let $r$ be a CVRP route: a walk $0\to r_1\to\cdots\to r_m\to 0$ in $G$, $m\ge 1$, visiting pairwise distinct clients with total demand at most $C$. Then $r$ is a q-route without 2-cycles:
--   $$\{\text{CVRP routes}\}\subseteq\{\text{q-routes without 2-cycles}\}.$$
--
--   This containment is what makes the column formulation $P_2$ a relaxation of the CVRP: every vehicle route of a feasible solution is available as a column.
--
--   **Formalization Note** The paper says the containment is strict. Strictness depends on the instance (for instance, it fails when $C$ is smaller than twice every client demand, since then no q-route can repeat a client), so only the containment is stated.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 2, §1, definition of q-routes; p. 4, §2, q-routes without 2-cycles

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem route_isQRoute {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (C : ℕ) (r : List (Fin (n + 1))) (hr : IsRoute E d C r) :
    IsQRoute E d C r := by sorry
end RobustBCPCVRP.Formulation
