-- Prove2me | Theorems.Thm_SendSplit_DPEquations_eq6_split_le
-- name    : SendSplit.DPEquations.eq6_split_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:25:49.890951+00:00
-- url     : https://prove2.me/theorems/3df4d55c-03b3-45d7-9cbf-bd8018bf6f4c
-- title:
--   Eq. (6) — C_iI ≤ C_iJ + C_{i,I∖J} for every nonempty proper subset J of I
-- statement:
--   Consider a network with arc costs concave on $[0,\infty)$ and vanishing at $0$, and suppose there is a minimum-cost flow for $r$. Let $i \in N$, $\emptyset \subset I \subseteq D$, and let $J$ be a nonempty proper subset of $I$. Then
--
--   $$C_{iI} \;\le\; C_{iJ} + C_{i, I \setminus J}. \qquad (6)$$
--
--   The sum of flows for the subproblems $i \to J$ and $i \to (I \setminus J)$ is a flow for $i \to I$; if one of these subproblems has no flow, the right side is $+\infty$.
--
--   **Formalization Note** The existence of a minimum-cost flow (the hypothesis of Theorem 2) guarantees that no $C$ value is $-\infty$, so the extended-real sum on the right is the paper's sum.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 641, Eq. (6)

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem eq6_split_le {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (hmin : ∃ x, IsMinCostFlow A c r x)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (J : Finset (Fin n)) (hJne : J.Nonempty) (hJI : J ⊆ I) (hJI' : J ≠ I) :
    minCost A c r i I ≤ minCost A c r i J + minCost A c r i (I \ J) := by sorry

end SendSplit.DPEquations
