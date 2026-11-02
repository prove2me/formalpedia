-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_partition_strict_even_target_exists
-- name    : TwoAgentSched.TotalTotal.partition_strict_even_target_exists
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:00:56.040075+00:00
-- url     : https://prove2.me/theorems/1145e2a9-7b9a-4970-8857-8bcc9dcbbc7d
-- title:
--   Every finite PARTITION instance has an equivalent strictly increasing even scheduling code
-- statement:
--   Let $w_1,\ldots,w_n$ be arbitrary nonnegative integers, including zero and repeated values. There are nonnegative integers $p_1<\cdots<p_k$, all even, and a nonnegative integer $q$ such that the common real threshold of the scheduling instance constructed from $p$ is $q$ and
--
--   $$
--   \text{the weights }w_1,\ldots,w_n\text{ admit an equal-sum partition}
--   \quad\Longleftrightarrow\quad
--   \text{the canonical code of the constructed scheduling instance with bounds }(q,q)\text{ belongs to the target language}.
--   $$
--
--   This existential bridge applies the corrected distinct-weight equivalence from the proof of Theorem 9.2. The conversion from arbitrary weights to strictly increasing even weights is an additional finite gadget, not a claim stated in the cited paper. This theorem does not assert that the conversion is computable in polynomial time; an explicit encoded transducer and its runtime bound remain necessary for the complexity reduction.
--
--   **Formalization Note** The empty input and zero weights are allowed. The target language uses the canonical binary encoding of both job counts, both processing-time lists, and the two natural-number bounds.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2 and proof, pp. 237–238. The arbitrary-to-distinct-even partition gadget and encoded existential bridge are additional supporting arguments, not statements claimed in the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Construction

namespace TwoAgentSched.TotalTotal

open ProjSchedTW.Complexity

theorem partition_strict_even_target_exists {n : ℕ} (w : Fin n → ℕ) :
    ∃ (k : ℕ) (p : Fin k → ℕ) (q : ℕ), StrictMono p ∧
      (∀ i, Even (p i)) ∧ thresholdQ p = (q : ℝ) ∧
      (PartitionYes (List.ofFn w) ↔
        encNats ((construction p).codeList q q) ∈ targetLang) := by sorry

end TwoAgentSched.TotalTotal
