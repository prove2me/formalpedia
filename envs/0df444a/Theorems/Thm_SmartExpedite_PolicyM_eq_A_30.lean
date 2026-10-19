-- Prove2me | Theorems.Thm_SmartExpedite_PolicyM_eq_A_30
-- name    : SmartExpedite.PolicyM.eq_A_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:22.654414+00:00
-- url     : https://prove2.me/theorems/7d99bfa8-1164-4306-8153-bb0f6f42fb99
-- title:
--   (A-30), p. 37 — equality of the proof sets A_m and B_m on their defined range
-- statement:
--   Let $K\ge1$ and let $u$ be Policy-M parameters satisfying Assumption A. For $2\le i\le K$ and $1\le m\le i-2$, let $A_m$ and $B_m$ be the state subsets in (A-16) and (A-17), for the fixed receiving node $i$. Then
--
--   $$A_m=B_m.$$
--
--   This identifies a full family of strict segment constraints with the single family at endpoint $i-1$ used in the indicator partition.
--
--   **Formalization Note** The printed range in (A-30) extends to $m=i-1$, while (A-16)–(A-17) define these sets only through $i-2$. This statement uses their defined range.
-- source:
--   Song, Xiao, Zhang & Zipkin, Smart policies for multi-source inventory systems and general tandem queues with order tracking and expediting, SSRN 3702068 (version of September 28, 2020), pp. 35–38, (A-16)–(A-18), (A-30)–(A-39)

import Mathlib
import Definitions.Def_SmartExpedite_PolicyM_Model

namespace SmartExpedite.PolicyM

/-- Equation (A-30), p. 37, on the index range where (A-16) and (A-17)
actually define `A_m` and `B_m`: `1 ≤ m ≤ i - 2`. -/
theorem eq_A_30 (K : ℕ) (u : ℕ → ℕ → ℕ∞)
    (hK : 1 ≤ K) (hu : IsPolicyParam K u) (hA : AssumptionA K u) :
    ∀ i m, 1 ≤ m → m + 2 ≤ i → i ≤ K → Aset K u i m = Bset K u i m := by sorry

end SmartExpedite.PolicyM
