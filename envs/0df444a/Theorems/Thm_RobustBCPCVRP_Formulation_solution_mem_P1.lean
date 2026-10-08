-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_solution_mem_P1
-- name    : RobustBCPCVRP.Formulation.solution_mem_P1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:14.5144+00:00
-- url     : https://prove2.me/theorems/ac67f280-b0c0-4bca-a81f-5707ae762743
-- title:
--   §2, p. 4 — the edge vector of every CVRP solution lies in P₁, and its cost is ℓᵀx
-- statement:
--   Let $G=(V,E)$, demands $d$, $K$ vehicles, capacity $C$ and edge lengths $\ell$ be given, and let $R=(R_1,\dots,R_K)$ be a feasible CVRP solution: $K$ routes from the depot, each visiting distinct clients with total demand at most $C$, every client visited exactly once overall. Let $x=\chi(R)$, $x_e$ being the number of times the routes traverse $e$. Then
--   $$x\in P_1\qquad\text{and}\qquad \sum_{e\in E}\ell_e x_e=\text{total length of the routes of }R .$$
--
--   So constraints (1)–(4) are valid for the CVRP: (1) every client is entered and left once, (2) $K$ vehicles leave and enter the depot, (3) every client set is served by at least $\lceil d(S)/C\rceil$ vehicles, and (4) every edge away from the depot is used at most once. With the cost identity this makes $\min_{x\in P_1}\ell^\top x$ a lower bound on the CVRP optimum.
--
--   **Formalization Note** The cost identity is not stated separately in the paper; it is bundled here because it is what turns "$x\in P_1$" into the bound $L_1\le\mathrm{OPT}$. No hypothesis on the instance is needed (positive demands, positive capacity, nonnegative lengths and a loop-free graph are not used).
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 4, §2, after the display of P₁ (1)–(4)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem solution_mem_P1 {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (R : Fin K → List (Fin (n + 1))) (hR : IsCVRPSolution E d K C R) :
    InP1 E d K C (chi R) ∧ ∑ e ∈ E, ℓ e * chi R e = cost ℓ R := by sorry
end RobustBCPCVRP.Formulation
