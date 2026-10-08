-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_solution_mem_P2
-- name    : RobustBCPCVRP.Formulation.solution_mem_P2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:59.205132+00:00
-- url     : https://prove2.me/theorems/3788cb89-4934-4728-a566-54e2af221777
-- title:
--   §2, p. 4 — the edge vector of every CVRP solution lies in P₂, with its routes as columns
-- statement:
--   Let $R=(R_1,\dots,R_K)$ be a feasible CVRP solution of an instance with graph $G=(V,E)$, demands $d$, $K$ vehicles and capacity $C$, and let $\lambda^R=\sum_{k=1}^K \mathbf 1_{R_k}$ put weight one on each of its routes. Then
--
--   1. $\lambda^R$ is a family of columns: its support consists of q-routes without 2-cycles with nonnegative weights;
--   2. (5) holds: $\sum_r q^e(r)\lambda^R_r=\chi(R)_e$ for every $e\in E$;
--   3. (6) holds: $\sum_r\lambda^R_r=K$;
--   4. consequently $\chi(R)\in P_2$.
--
--   This is the validity half of the paper's claim that the integer vectors of $P_2$ are exactly the CVRP solutions: every solution is represented in the column formulation, with its own routes as the columns.
--
--   **Formalization Note** The routes of a solution are nonempty and pairwise disjoint, hence pairwise distinct, so $\lambda^R$ is their $0/1$ indicator. No hypothesis on the instance is needed.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 4, §2, after the display of P₂ (5)–(6)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem solution_mem_P2 {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (R : Fin K → List (Fin (n + 1))) (hR : IsCVRPSolution E d K C R) :
    IsColumns E d C (∑ k, Finsupp.single (R k) (1 : ℝ)) ∧
      (∀ e ∈ E, colSum (∑ k, Finsupp.single (R k) (1 : ℝ)) e = chi R e) ∧
      colCount (∑ k, Finsupp.single (R k) (1 : ℝ)) = (K : ℝ) ∧
      InP2 E d K C (chi R) := by sorry
end RobustBCPCVRP.Formulation
