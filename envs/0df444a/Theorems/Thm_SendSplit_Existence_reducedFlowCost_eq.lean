-- Prove2me | Theorems.Thm_SendSplit_Existence_reducedFlowCost_eq
-- name    : SendSplit.Existence.reducedFlowCost_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:24:06.961406+00:00
-- url     : https://prove2.me/theorems/1febf7a7-62b2-4910-87ca-b5c4289b3249
-- title:
--   §2, p. 639 — for each flow, $c^\pi(x) = c(x) + \sum_i \pi_i r_i$
-- statement:
--   Let $G$ be a graph, $c_{ij}$ arbitrary arc cost functions, $\pi \in \mathbb{R}^n$ and $r$ a demand vector. For every flow $x$ for $r$,
--
--   $$c^\pi(x) = c(x) + \sum_i \pi_i r_i,$$
--
--   where $c^\pi(x) = \sum_{(i,j)\in A}\big(c_{ij}(x_{ij}) - (\pi_i - \pi_j)x_{ij}\big)$.
--
--   Hence the set of flows minimizing $c^\pi$ does not depend on $\pi$, and on circulations $c^\pi = c$; this is how condition 7° yields 4°.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Section 2

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_ReducedCost

namespace SendSplit.Existence

theorem reducedFlowCost_eq {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (π : Fin n → ℝ) (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x) :
    reducedFlowCost G c π x = flowCost G c x + ∑ i, π i * r i := by sorry

end SendSplit.Existence
