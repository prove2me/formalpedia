-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_integer_P1_is_solution
-- name    : RobustBCPCVRP.Formulation.integer_P1_is_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:04.63006+00:00
-- url     : https://prove2.me/theorems/a6fa694f-4ca6-4dc4-bf30-9b4241e0d133
-- title:
--   §2, p. 4 — every integer point of P₁ is the edge vector of a CVRP solution
-- statement:
--   Let $G=(V,E)$ be a graph without loops on $V=\{0,\dots,n\}$, with positive client demands $d_i>0$ ($i\in V_+$), $K>0$ vehicles and positive capacity $C>0$. If $x\in P_1$ and every coordinate of $x$ is an integer, then there is a feasible CVRP solution $R=(R_1,\dots,R_K)$ with
--   $$x=\chi(R),$$
--   i.e. $x_e$ is the number of times the routes of $R$ traverse $e$.
--
--   Together with the validity of (1)–(4) this says that the integer vectors of $P_1$ are exactly the CVRP solutions, so $P_1$ is a correct integer formulation and branching on $x$ is a correct exact method.
--
--   **Formalization Note** Positive demands and positive capacity are standing assumptions of the paper (p. 1) and are needed: with a zero demand or $C=0$, the right-hand side $2k(S)$ of (3) can vanish on a client-only cycle. The loop-free hypothesis is needed because a loop at a client is invisible to the cut constraints. $K>0$ is the paper's standing assumption that the number of vehicles is a positive integer (p. 1); $\ell\ge 0$ is not needed and is omitted.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 4, §2, 'The integer vectors x in P1 define all feasible solutions for the CVRP'

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem integer_P1_is_solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ i : Fin (n + 1), i ≠ 0 → 0 < d i) (hK : 0 < K) (hC : 0 < C)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : InP1 E d K C x) (hxZ : IsIntegerVec x) :
    ∃ R : Fin K → List (Fin (n + 1)), IsCVRPSolution E d K C R ∧ x = chi R := by sorry
end RobustBCPCVRP.Formulation
