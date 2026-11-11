-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_A_4
-- name    : UnequalHuffman.NPC.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:21.845701+00:00
-- url     : https://prove2.me/theorems/166b24a6-9110-43f2-b269-5848e5f8f310
-- title:
--   Lemma A.4 — the five-level exchange {−1, b} → {b, 4} of Table 6 (explicit construction of the proof)
-- statement:
--   For $b \in \{0,1\}$ and the five-level construction of Table 6 (`exchangeData`): there is a sequence from $\{-1, b\}$ satisfying the prescribed leaf counts and intervals that ends in $\{b, 4\}$ and has score zero, and every other complete sequence satisfying the prescribed leaf counts and intervals (final multiset unrestricted) has score at least one.
--
--   Source (p. 42): "Lemma A.4. For each $b \in \{0,1\}$, there is a five-level construction whose unique minimum-score feasible sequence is a transition $\{-1, b\} \to \{b, 4\}$. Its score is zero. Every other complete sequence satisfying the prescribed leaf counts and intervals has score at least one, with no restriction on its final internal coordinates."
--
--   Differences from the source:
--   - generalization: there is a five-level construction → the explicit construction of the proof (Table 6, p. 42), exchangeData; reason: the explicit data implies the existential and is what Lemma 3.2's proof uses
--   - encoding: unique minimum-score feasible sequence with score zero, gap one → ∃ feasible X ending in {b, 4} with score 0, and every feasible Y ≠ X scores ≥ 1; reason: scores are integers
--   - encoding: sequence of coordinate multisets → X : Fin 6 → Multiset ℤ; reason: coordinates are integers
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 42, Lemma A.4 (Table 6)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Gadgets

namespace UnequalHuffman.NPC

open LeafData

/-- Lemma A.4 (p. 42), for the five-level exchange construction of Table 6 (`exchangeData`): for
`b ∈ {0, 1}`, there is a sequence from `{-1, b}` satisfying the prescribed leaf counts and
intervals that ends in `{b, 4}` with score zero, and every other such sequence (final multiset
unrestricted) has score at least one. -/
theorem lemma_A_4 (b : ℤ) (hb : b = 0 ∨ b = 1) :
    ∃ X : Fin (exchangeData.length + 1) → Multiset ℤ,
      exchangeData.IsFeasibleSeq {-1, b} X ∧ X (Fin.last _) = {b, 4} ∧
      exchangeData.score X = 0 ∧
      ∀ Y : Fin (exchangeData.length + 1) → Multiset ℤ,
        exchangeData.IsFeasibleSeq {-1, b} Y → Y ≠ X → 1 ≤ exchangeData.score Y := by sorry

end UnequalHuffman.NPC
