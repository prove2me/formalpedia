-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_A_5
-- name    : UnequalHuffman.NPC.lemma_A_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:25.387688+00:00
-- url     : https://prove2.me/theorems/814a0b52-1e99-4781-826c-7917d610b754
-- title:
--   Lemma A.5 — the wait and move operations have unique minimum-score sequences with gap one
-- statement:
--   1. For every $d \ge 3$, every base $r \in \mathbb Z$ and $b \in \{0,1\}$, the $d$-level wait operation (one leaf per level in $[r+1, r+2]$, coefficients $d-1, -1, \dots, -1$ in level order) has a complete sequence from $\{r+b\}$ that keeps $\{r+b\}$ at every level and has score zero, and every other complete sequence satisfying the leaf data scores at least one.
--   2. For every $r \in \mathbb Z$ and $b \in \{0,1\}$, the three-level move operation (leaf intervals $[r+1,r+2], [r+1,r+2], [r,r+1]$, coefficients $-1, 0, 1$) has a complete sequence from $\{r+b\}$ ending at $\{r+1+b\}$ with score $-1$, and every other complete sequence satisfying the leaf data scores at least $0$.
--
--   Source (p. 43): "Lemma A.5. The following operations have unique minimum-score sequences, with a gap of at least one to every other complete sequence satisfying their leaf data. 1. For every $d \ge 3$, a $d$-level operation retains the bit at $r + b$ with score zero. At each level it creates one leaf in $[r+1, r+2]$, with coefficients $d-1, -1, \dots, -1$ in level order. 2. A three-level operation moves the bit from $r + b$ to $r + 1 + b$ with score $-1$. Its successive leaf intervals are $[r+1, r+2], [r+1, r+2], [r, r+1]$, and the corresponding coefficients are $-1, 0, 1$."
--
--   Differences from the source:
--   - encoding: retains the bit at r + b; moves the bit from r + b to r + 1 + b → the minimizing sequence is {r + b} at every level (wait), and ends at {r + 1 + b} (move); reason: the bit b ∈ {0, 1} is stored as the coordinate r + b of one internal vertex
--   - encoding: unique minimum-score sequence with a gap of at least one → ∃ feasible X with the stated score, and every feasible Y ≠ X scores ≥ that score + 1; reason: scores are integers; complete sequence = prescribed counts and intervals
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 43, Lemma A.5

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Gadgets

namespace UnequalHuffman.NPC

open LeafData

/-- Lemma A.5 (p. 43). (1) For every `d ≥ 3`, base `r ∈ ℤ` and bit `b ∈ {0, 1}`, the `d`-level
wait operation (one leaf per level in `[r+1, r+2]`, coefficients `d - 1, -1, …, -1`) has a unique
minimum-score complete sequence from `{r + b}`: it retains the bit at `r + b` at every level, has
score zero, and every other complete sequence satisfying the leaf data scores at least one.
(2) For every `r` and `b`, the three-level move operation (leaf intervals `[r+1, r+2]`,
`[r+1, r+2]`, `[r, r+1]`, coefficients `-1, 0, 1`) has a unique minimum-score complete sequence
from `{r + b}`, ending at `{r + 1 + b}` with score `-1`, and every other complete sequence
satisfying the leaf data scores at least `0`. -/
theorem lemma_A_5 :
    (∀ (d : ℕ) (r b : ℤ), 3 ≤ d → (b = 0 ∨ b = 1) →
      ∃ X : Fin ((waitData d r).length + 1) → Multiset ℤ,
        (waitData d r).IsFeasibleSeq {r + b} X ∧ (∀ j, X j = {r + b}) ∧
        (waitData d r).score X = 0 ∧
        ∀ Y : Fin ((waitData d r).length + 1) → Multiset ℤ,
          (waitData d r).IsFeasibleSeq {r + b} Y → Y ≠ X → 0 + 1 ≤ (waitData d r).score Y) ∧
    (∀ r b : ℤ, (b = 0 ∨ b = 1) →
      ∃ X : Fin ((moveData r).length + 1) → Multiset ℤ,
        (moveData r).IsFeasibleSeq {r + b} X ∧ X (Fin.last _) = {r + 1 + b} ∧
        (moveData r).score X = -1 ∧
        ∀ Y : Fin ((moveData r).length + 1) → Multiset ℤ,
          (moveData r).IsFeasibleSeq {r + b} Y → Y ≠ X → -1 + 1 ≤ (moveData r).score Y) := by sorry

end UnequalHuffman.NPC
