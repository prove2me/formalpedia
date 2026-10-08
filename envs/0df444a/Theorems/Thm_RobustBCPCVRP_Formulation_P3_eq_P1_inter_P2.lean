-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_P3_eq_P1_inter_P2
-- name    : RobustBCPCVRP.Formulation.P3_eq_P1_inter_P2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:51.453299+00:00
-- url     : https://prove2.me/theorems/1392a949-28a7-4f5f-a506-e297ab8a6e2c
-- title:
--   §2, p. 5 — the Explicit Master describes P₃ = P₁ ∩ P₂
-- statement:
--   Let $G=(V,E)$, demands $d$, $K$ vehicles and capacity $C$ be a CVRP instance, and let $P_1$, $P_2$ be the polytopes of the paper and $P_3$ the projection onto $x$ of the Explicit Master system (1)–(6), $x\ge 0$, $\lambda\ge 0$, in which one vector $\lambda$ of q-route weights serves both (5) and (6). Then
--   $$P_3=P_1\cap P_2 .$$
--
--   The paper's new formulation optimizes over the intersection of the cut polytope $P_1$ and the q-route polytope $P_2$; this statement identifies that intersection with the single lifted system the algorithm actually works with.
--
--   **Formalization Note** No hypothesis on the instance is needed. Membership is stated for every function $x$ on unordered pairs; each of $P_1,P_2,P_3$ requires $x$ to vanish off $E$.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 5, §2, display of P₃ (left-hand side P₃ = P₁∩P₂)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem P3_eq_P1_inter_P2 {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ) :
    InP3 E d K C x ↔ InP1 E d K C x ∧ InP2 E d K C x := by sorry
end RobustBCPCVRP.Formulation
