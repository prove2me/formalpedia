-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_eq_A_5
-- name    : SmartExpedite.PolicyM.eq_A_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:23.225746+00:00
-- url     : https://prove2.me/theorems/3fad76c4-0742-437a-8b6b-f4a4fc7b809f
-- title:
--   (A-5), pp. 33–34 — Policy-M expediting preserves the admissible state set
-- statement:
--   Let $K\ge1$ and let $u$ be Policy-M parameters satisfying Assumption A. Suppose $n\in S_M(u)$ and node $m<K$ contains at least one unit. If the expediting rule sends a completed unit from $m$ to node $j$, then
--
--   $$n-e_m+e_j\in S_M(u).$$
--
--   This is the service-routing half of the state-space closure argument for Theorem 1.
--
--   **Formalization Note** The positive occupancy condition enables the service completion and prevents truncated subtraction from representing a departure at an empty node.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), pp. 33–34, (A-5)–(A-11)

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

/-- Equation (A-5), pp. 33–34. The positivity guard implements the paper's
service indicator and prevents truncated natural subtraction at an empty node. -/
theorem eq_A_5 (K : ℕ) (u : ℕ → ℕ → ℕ∞)
    (hK : 1 ≤ K) (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    ∀ n ∈ SM K u, ∀ m, 1 ≤ m → m ≤ K - 1 → 0 < occ n m →
      n - ev K m + ev K (expNode K u m n) ∈ SM K u := by sorry

end SmartExpedite.PolicyM
