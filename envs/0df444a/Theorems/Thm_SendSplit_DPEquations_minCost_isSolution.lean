-- Prove2me | Theorems.Thm_SendSplit_DPEquations_minCost_isSolution
-- name    : SendSplit.DPEquations.minCost_isSolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:39:38.832356+00:00
-- url     : https://prove2.me/theorems/2d633a4e-0ebe-4182-b16d-639ae08d1d89
-- title:
--   Proof of Theorem 2, p. 642 — the subproblem minimum costs C satisfy (1) and (2)
-- statement:
--   Consider a network with arc costs concave on $[0,\infty)$ and vanishing at $0$, and suppose there is a minimum-cost flow for $r$. Then the array $C = (C_{jI})$, $j \in N$, $\emptyset \subset I \subseteq D$, of subproblem minimum costs is a **$+\infty$ or real-valued solution of (1) and (2)** with $B$ defined by (3): no $C_{jI}$ equals $-\infty$; $C_{iI} = C_{jI_j}$ for $j \in I$ when $r_I = 0$; and
--
--   $$C_{iI} \;=\; \min_{(i,j)\in A_I} \bigl[ c_{ij}(r_I) + C_{jI} \bigr] \;\wedge\; B_{iI}$$
--
--   when $r_I \neq 0$.
--
--   This is the first half of Theorem 2 ("$C$ is a solution"); the paper's argument for $i \notin I$ inspects the forest induced by an extreme minimum-cost flow of the subproblem.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), pp. 641–642, Section 3, proof of Theorem 2

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations

namespace SendSplit.DPEquations

theorem minCost_isSolution {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x) :
    IsSolution A c r (minCost A c r) := by sorry

end SendSplit.DPEquations
