-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_A_2
-- name    : UnequalHuffman.NPC.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:29.721063+00:00
-- url     : https://prove2.me/theorems/d252c658-8058-4eb2-be28-62014007490d
-- title:
--   Lemma A.2 — the six-level Copy construction {b} → {1 + b, 5 + b} (explicit construction of the proof)
-- statement:
--   For $b \in \{0,1\}$ and the six-level construction of the proof (`copyData`: no leaves at levels 1–4; 30 leaves at level 5 with coefficient $0$ and intervals $[1,2]^{\times 5}, [2,3]^{\times 10}, [3,4]^{\times 10}, [4,5]^{\times 5}$; two leaves at level 6 with intervals $[0,1], [6,7]$ and coefficients $1, -1$): all leaf intervals have width one, and there is a sequence of coordinate multisets from $\{b\}$ with the prescribed leaf counts that ends in $\{1+b, 5+b\}$, has score $-6$ and satisfies the leaf intervals, while every other sequence from $\{b\}$ with the prescribed leaf counts (intervals not required, final multiset unrestricted) has score at least $-5$.
--
--   Source (p. 41): "Lemma A.2. For each $b \in \{0,1\}$, there is a six-level construction whose unique minimum-score sequence of coordinate multisets is a transition $\{b\} \to \{1+b, 5+b\}$. Its score is $-6$, and every other sequence with the prescribed leaf counts has score at least $-5$, with no restriction on its final internal coordinates. The minimum-score sequence satisfies the prescribed leaf intervals, all of which have width one."
--
--   Differences from the source:
--   - generalization: there is a six-level construction → the explicit construction of the proof (p. 41), copyData; reason: the explicit data implies the existential and is what Lemma 3.2's proof uses
--   - encoding: unique minimum-score sequence, score −6, every other sequence ≥ −5 → ∃ X with counts, final {1 + b, 5 + b}, score −6 and intervals, and every Y ≠ X with the counts scores ≥ −5; reason: scores are integers, so this is the unique minimum with its gap
--   - encoding: sequence of coordinate multisets X_0, …, X_6 → X : Fin 7 → Multiset ℤ; b ∈ {0, 1} as an integer; reason: coordinates relative to base 0, integers
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 41, Lemma A.2 (construction from its proof)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Gadgets

namespace UnequalHuffman.NPC

open LeafData

/-- Lemma A.2 (p. 41), for the six-level Copy construction of its proof (`copyData`): for
`b ∈ {0, 1}`, all its leaf intervals have width one, and there is a sequence of coordinate
multisets from `{b}` with the prescribed leaf counts that ends in `{1 + b, 5 + b}`, has score
`-6` and satisfies the leaf intervals, while every other sequence from `{b}` with the prescribed
leaf counts (intervals not required, final multiset unrestricted) has score at least `-5`. -/
theorem lemma_A_2 (b : ℤ) (hb : b = 0 ∨ b = 1) :
    (∀ lvl ∈ copyData, ∀ p ∈ lvl, p.2.1 - p.1 = 1) ∧
    ∃ X : Fin (copyData.length + 1) → Multiset ℤ,
      copyData.IsSeq {b} X ∧ X (Fin.last _) = {1 + b, 5 + b} ∧ copyData.score X = -6 ∧
      copyData.SatisfiesIntervals X ∧
      ∀ Y : Fin (copyData.length + 1) → Multiset ℤ, copyData.IsSeq {b} Y → Y ≠ X →
        -5 ≤ copyData.score Y := by sorry

end UnequalHuffman.NPC
