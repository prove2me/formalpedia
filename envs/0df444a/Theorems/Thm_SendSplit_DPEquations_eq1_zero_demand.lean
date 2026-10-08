-- Prove2me | Theorems.Thm_SendSplit_DPEquations_eq1_zero_demand
-- name    : SendSplit.DPEquations.eq1_zero_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:25:27.043619+00:00
-- url     : https://prove2.me/theorems/56112ed0-8a80-40d9-a95a-d7dd96d0e91d
-- title:
--   Eq. (1) — if r_I = 0 then C_iI = C_{j,I∖{j}} for every j ∈ I
-- statement:
--   In the network model with concave arc costs vanishing at $0$, let $i \in N$ and $\emptyset \subset I \subseteq D$ with $r_I = \sum_{j\in I} r_j = 0$. Then for every $j \in I$, writing $I_j = I \setminus \{j\}$,
--
--   $$C_{iI} \;=\; C_{j I_j}. \qquad (1)$$
--
--   This is equation (1) of the send-and-split method: when the demands in $I$ balance, the subproblem does not depend on the node $i$ at which $r_I$ is subtracted. With $I = D$ it gives the observation of p. 640 that the minimum cost of the original problem is $C_{iD} = C_{jD_j}$.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 640, Eq. (1)

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

theorem eq1_zero_demand {n : ℕ} (A : Finset (Fin n × Fin n))
    (c : Fin n → Fin n → ℝ → ℝ) (r : Fin n → ℝ)
    (hA : IsGraph A) (hc : IsConcaveArcCost A c)
    (i : Fin n) (I : Finset (Fin n)) (hI : IsAdmissible r I) (hrI : demandSum r I = 0)
    (j : Fin n) (hj : j ∈ I) :
    minCost A c r i I = minCost A c r j (I.erase j) := by sorry

end SendSplit.DPEquations
