-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_eq_A_2
-- name    : SmartExpedite.PolicyM.eq_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:27.562479+00:00
-- url     : https://prove2.me/theorems/fc8ba751-d378-4069-81ad-29a009a38a75
-- title:
--   (A-2), p. 33 — Policy-M arrivals preserve the admissible state set
-- statement:
--   Let $K\ge1$ and let $u$ be Policy-M parameters satisfying Assumption A. For an admissible occupancy vector $n\in S_M(u)$, let $i$ be the order destination selected by the demand routing rule (7). Then
--
--   $$n+e_i\in S_M(u).$$
--
--   This is the arrival half of the state-space closure argument for Theorem 1.
--
--   **Formalization Note** The empty maximum in (7) routes an order to node 1; the helper selecting $i$ implements this convention.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), p. 33, (A-1)–(A-2)

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

/-- Equation (A-2), p. 33. Equation (A-1) characterizes the arrival destination
selected by `arrNode`; this states that such an arrival preserves (11). -/
theorem eq_A_2 (K : ℕ) (u : ℕ → ℕ → ℕ∞)
    (hK : 1 ≤ K) (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    ∀ n ∈ SM K u, n + ev K (arrNode K u n) ∈ SM K u := by sorry

end SmartExpedite.PolicyM
