-- Prove2me | Theorems.Thm_SendSplit_DPEquations_eq4_subadditive
-- name    : SendSplit.DPEquations.eq4_subadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:25:37.814901+00:00
-- url     : https://prove2.me/theorems/eb93bf01-b5fc-4949-913c-445a33d8ce46
-- title:
--   Eq. (4) — C_iI ≤ c(x) + c(y) whenever x + y is a flow for the subproblem i → I
-- statement:
--   In the network model with arc costs concave on $[0,\infty)$ and vanishing at $0$, let $i \in N$ and $\emptyset \subset I \subseteq D$. If $x$ and $y$ are preflows such that $x + y$ is a flow for the subproblem $i \to I$, then
--
--   $$C_{iI} \;\le\; c(x) + c(y). \qquad (4)$$
--
--   It combines $C_{iI} \le c(x+y)$ with the subadditivity of the flow cost, and is the common step behind (5) and (6).
--
--   **Formalization Note** The paper states (4) under the standing supposition "$C_{iI}$ is finite"; the inequality is true without it, so that supposition is not a hypothesis here.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 641, Eq. (4)

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem eq4_subadditive {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (x y : Fin n → Fin n → ℝ) (hx : IsPreflow A x) (hy : IsPreflow A y)
    (hxy : IsFlow A (subDemand r i I) (x + y)) :
    minCost A c r i I ≤ ((flowCost A c x + flowCost A c y : ℝ) : EReal) := by sorry

end SendSplit.DPEquations
