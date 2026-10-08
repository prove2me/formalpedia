-- Prove2me | Theorems.Thm_SendSplit_DPEquations_theorem2_dp_equations
-- name    : SendSplit.DPEquations.theorem2_dp_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:39:45.455822+00:00
-- url     : https://prove2.me/theorems/4aa34c95-91ae-42ef-aaac-fb0ea1e0bc90
-- title:
--   Theorem 2 (Dynamic-Programming Equations) — C is the greatest +∞-or-real solution of (1) and (2), and the only one if simple circulations cost positively
-- statement:
--   **Theorem 2 (Dynamic-Programming Equations).** Let $(G, r)$ be a network whose arc costs $c_{ij}$ are concave on $[0,\infty)$ with $c_{ij}(0) = 0$, and let $C = (C_{jI})$, $j \in N$, $\emptyset \subset I \subseteq D$, be the array of subproblem minimum costs. If there is a minimum-cost flow for $r$, then $C$ is the **greatest $+\infty$ or real-valued solution** of (1) and (2) (with $B$ defined by (3)):
--
--   1. $C$ is a $+\infty$ or real-valued solution of (1) and (2);
--   2. every $+\infty$ or real-valued solution $C'$ of (1) and (2) satisfies
--   $$C'_{jI} \;\le\; C_{jI} \qquad \text{for all } j \in N,\ \emptyset \subset I \subseteq D .$$
--
--   If moreover **each simple circulation has positive cost**, then $C$ is the **only** such solution: every $+\infty$ or real-valued solution $C'$ of (1) and (2) equals $C$ on all $j \in N$ and $\emptyset \subset I \subseteq D$.
--
--   In particular the minimum cost of the original problem, $C_{iD} = C_{jD_j}$, is determined by the equations. Without the positivity hypothesis uniqueness can fail: if every $c_{ij} \equiv 0$, $r_I \neq 0$ for all nonempty proper subsets $I$ of $D$, and $G$ is strongly connected, then $C = 0$ while $C'_{iI} = -(|I| \wedge d)$ also solves (1) and (2) (p. 641).
--
--   **Formalization Note** "+∞ or real-valued" is the condition $C'_{jI} \neq -\infty$ on every admissible $I$; for $C$ it is part of the first conclusion. "Greatest" is stated as two claims, that $C$ is a solution and that it dominates every solution. "Each simple circulation has positive cost" quantifies over every simple circuit and every flow value $\theta > 0$ on it. Arrays are compared only on $\emptyset \subset I \subseteq D$.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 641, Theorem 2

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations

namespace SendSplit.DPEquations

theorem theorem2_dp_equations {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x) :
    IsSolution A c r (minCost A c r) ∧
      (∀ C' : Fin n → Finset (Fin n) → EReal, IsSolution A c r C' →
        ∀ j I, IsAdmissible r I → C' j I ≤ minCost A c r j I) ∧
      ((∀ y, IsSimpleCirculation A y → 0 < flowCost A c y) →
        ∀ C' : Fin n → Finset (Fin n) → EReal, IsSolution A c r C' →
          ∀ j I, IsAdmissible r I → C' j I = minCost A c r j I) := by sorry

end SendSplit.DPEquations
