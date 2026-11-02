-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_ordered_partition_gadget_target
-- name    : TwoAgentSched.TotalTotal.ordered_partition_gadget_target
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:56:30.549416+00:00
-- url     : https://prove2.me/theorems/7c9df31e-2029-46f7-bb08-76be057f8701
-- title:
--   A directly ordered even gadget preserves the exact scheduling target code
-- statement:
--   Let $w_1,\ldots,w_n$ be positive natural weights below $2^N$, and let $p$ be the directly ordered even gadget obtained by listing its two tagged weights for each index in order. There is a natural threshold $q$ such that:
--
--   1. $p$ is strictly increasing and every $p_j$ is even;
--   2. each $p_j$ has at most $N+3n+2$ binary digits;
--   3. $q$ equals the real threshold used in the scheduling construction; and
--   4. the original PARTITION instance is a yes-instance exactly when the canonical code of the constructed scheduling instance with both bounds $q$ lies in the target language.
--
--   The increasing order follows from the index-dependent high offsets, so no sorting operation is needed for this gadget. The construction and its bit-size bound are additional supporting results; the corrected distinct-weight scheduling equivalence comes from the formalized proof of Theorem 9.2. This theorem does not assert that the transformation can be computed in polynomial time. Zero input weights require separate removal.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2 and proof, pp. 237–238. The directly ordered even gadget and its size bound are additional supporting arguments, not claims of the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction
import Definitions.Def_TwoAgentSched_TotalTotal_OrderedPartitionGadget

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity StrictPartition

theorem ordered_partition_gadget_target {n : ℕ} (w : Fin n → ℕ) (N : ℕ)
    (hpos : ∀ i, 0 < w i) (hbound : ∀ i, w i < 2 ^ N) :
    ∃ q : ℕ, StrictMono (orderedEnum w N) ∧
      (∀ t, Even (orderedEnum w N t) ∧ (orderedEnum w N t).bits.length ≤ N + 3 * n + 2) ∧
      thresholdQ (orderedEnum w N) = (q : ℝ) ∧
      (PartitionYes (List.ofFn w) ↔
        encNats ((construction (orderedEnum w N)).codeList q q) ∈ targetLang) := by sorry

end TwoAgentSched.TotalTotal
