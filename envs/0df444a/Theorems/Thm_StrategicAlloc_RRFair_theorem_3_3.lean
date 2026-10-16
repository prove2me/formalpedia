-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_theorem_3_3
-- name    : StrategicAlloc.RRFair.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:46.132568+00:00
-- url     : https://prove2.me/theorems/ed5bf9b2-8497-4eb4-b283-ad9f25d7d4fa
-- title:
--   Theorem 3.3 — every PNE of Round-Robin is EF1 with respect to the true valuations
-- statement:
--   Let $N=[n]$ be $n\ge1$ agents with non-negative additive valuations $v_1,\dots,v_n$ on the goods $M=\{g_1,\dots,g_m\}$, and let $b=(b_1,\dots,b_n)$ be a pure Nash equilibrium of the Round-Robin mechanism (Mechanism 1, ties broken lexicographically): every $b_i$ is a non-negative bid vector, and no agent $i$ can obtain a bundle of larger true value $v_i$ by reporting any other non-negative bid vector. Then the allocation $(A_1,\dots,A_n)$ returned by Round-Robin$(b)$ is EF1 with respect to the true valuations: for all agents $i,j$ with $A_j\neq\emptyset$ there is a good $g\in A_j$ with
--   $$v_i(A_i)\ \ge\ v_i(A_j\setminus\{g\}).$$
--
--   Round-Robin is EF1 when agents report truthfully, but truth-telling is not an equilibrium. The theorem says that fairness survives strategic play: every stable outcome of the bidding game is EF1 for the agents' real preferences, although the mechanism never sees them. Valuations may have ties and zero values; $m$ need not be a multiple of $n$.
--
--   **Formalization Note.** Agents are `Fin n` with `[NeZero n]` and goods `Fin m`, both 0-based; agent 1 (`0`) picks first. `roundRobin` is Mechanism 1 with the lexicographic tie-breaking of line 4, `IsPNE` quantifies deviations over all of $\mathbb R^m_{\ge0}$, and EF1 is measured with $v$, not with the bids. `IsEF1` also quantifies over $i=j$, where it is trivial.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 8, Theorem 3.3

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Theorem 3.3 (p. 8): every PNE of Round-Robin is EF1 with respect to the true valuations. -/
theorem theorem_3_3 [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin n → Fin m → ℝ) (hpne : IsPNE roundRobin v b) :
    IsEF1 v (roundRobin b) := by sorry

end StrategicAlloc.RRFair
