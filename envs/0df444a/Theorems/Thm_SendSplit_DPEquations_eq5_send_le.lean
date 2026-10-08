-- Prove2me | Theorems.Thm_SendSplit_DPEquations_eq5_send_le
-- name    : SendSplit.DPEquations.eq5_send_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:39:43.92283+00:00
-- url     : https://prove2.me/theorems/17522dd9-d631-458e-82b9-e1f08f293a1a
-- title:
--   Eq. (5) — C_iI ≤ c_ij(r_I) + C_jI for every (i, j) ∈ A_I
-- statement:
--   In the network model with arc costs concave on $[0,\infty)$ and vanishing at $0$, let $\emptyset \subset I \subseteq D$ and let $(i, j) \in A_I$ (so $r_I \neq 0$). Then
--
--   $$C_{iI} \;\le\; c_{ij}(r_I) + C_{jI}, \qquad (5)$$
--
--   where $c_{ij}(r_I) = c_{ji}(-r_I)$ when $r_I < 0$. Sending $r_I$ along the arc from $i$ to $j$ and then solving the subproblem $j \to I$ gives a flow for the subproblem $i \to I$. If $C_{jI} = +\infty$ the inequality is trivial.
--
--   **Formalization Note** The page derives (5) inside the case "$C_{iI}$ finite" of the proof of Theorem 2; the inequality holds without that supposition and without the existence of a minimum-cost flow, so neither is a hypothesis. Extended-real addition of a real number and $C_{jI}$ is well defined in every case.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 641, Eq. (5)

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem
import Definitions.Def_SendSplit_DPEquations_Equations

namespace SendSplit.DPEquations

theorem eq5_send_le {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i j : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I)
    (hij : IsSendArc A r I i j) :
    minCost A c r i I ≤ sendCost A c r I i j + minCost A c r j I := by sorry

end SendSplit.DPEquations
