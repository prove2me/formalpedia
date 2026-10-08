-- Prove2me | Theorems.Thm_SendSplit_DPEquations_subproblem_attainment
-- name    : SendSplit.DPEquations.subproblem_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:25:35.504181+00:00
-- url     : https://prove2.me/theorems/efedccd2-d582-458e-84f1-ee0e2bc78a0e
-- title:
--   Section 3, p. 640 — each subproblem i → I has a minimum-cost flow (C_iI finite) or no flow (C_iI = +∞)
-- statement:
--   Consider a network $(G, r)$ whose arc costs $c_{ij}$ are concave on $[0, \infty)$ with $c_{ij}(0) = 0$, and suppose that **there is a minimum-cost flow** for $r$. Let $i \in N$ and $\emptyset \subset I \subseteq D$. Then exactly the alternative of p. 640 holds: either
--
--   1. there is a minimum-cost flow $x$ for the subproblem $i \to I$, and then $C_{iI} = c(x)$ is finite; or
--   2. there is no flow for the subproblem $i \to I$, and then $C_{iI} = +\infty$.
--
--   In particular $C_{iI} \neq -\infty$. The paper obtains this from Theorem 1, whose condition for the existence of a minimum-cost flow does not depend on the demand vector.
--
--   **Formalization Note** "$C_{iI}$ is finite" is rendered as $C_{iI} = c(x)$ for a minimum-cost flow $x$ of the subproblem.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 640, Section 3

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem subproblem_attainment {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I) :
    (∃ x, IsMinCostFlow A c (subDemand r i I) x ∧
        minCost A c r i I = ((flowCost A c x : ℝ) : EReal)) ∨
      ((∀ x, ¬ IsFlow A (subDemand r i I) x) ∧ minCost A c r i I = ⊤) := by sorry

end SendSplit.DPEquations
