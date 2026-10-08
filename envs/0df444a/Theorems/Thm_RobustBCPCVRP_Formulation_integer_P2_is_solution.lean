-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_integer_P2_is_solution
-- name    : RobustBCPCVRP.Formulation.integer_P2_is_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:09.888592+00:00
-- url     : https://prove2.me/theorems/1fa1d8b0-8a55-4e23-a1ba-1968d2714278
-- title:
--   §2, p. 4 — every integer point of P₂ is the edge vector of a CVRP solution
-- statement:
--   Let $G=(V,E)$ be a graph without loops on $V=\{0,\dots,n\}$, with positive client demands $d_i>0$, $K>0$ vehicles and positive capacity $C>0$. If $x\in P_2$ — that is, $x\ge 0$ satisfies (1) and $x=Q\lambda$ on $E$ for some weights $\lambda\ge 0$ on q-routes without 2-cycles with $\sum_j\lambda_j=K$ — and every coordinate of $x$ is an integer, then there is a feasible CVRP solution $R=(R_1,\dots,R_K)$ with
--   $$x=\chi(R).$$
--
--   With the validity of $P_2$ this is the paper's claim that the integer vectors of $P_2$ also define all feasible solutions of the CVRP: the q-route relaxation with 2-cycles removed is itself a correct integer formulation, even without the capacity cuts (3).
--
--   **Formalization Note** The paper states this without proof ("It can be shown"). The columns of $P_2$ are q-routes without 2-cycles, as in the paper's definition. Positive demands, a positive number of vehicles $K>0$, positive capacity and a loop-free graph are the paper's standing assumptions (p. 1); $\ell\ge 0$ is not needed and is omitted.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 4, §2, 'It can be shown that the set of integer vectors in P2 also defines all feasible solutions for the CVRP'

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem integer_P2_is_solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ i : Fin (n + 1), i ≠ 0 → 0 < d i) (hK : 0 < K) (hC : 0 < C)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : InP2 E d K C x) (hxZ : IsIntegerVec x) :
    ∃ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R ∧ x = chi R := by sorry
end RobustBCPCVRP.Formulation
