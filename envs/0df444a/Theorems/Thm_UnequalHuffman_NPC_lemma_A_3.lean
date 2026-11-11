-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_A_3
-- name    : UnequalHuffman.NPC.lemma_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:45:25.163282+00:00
-- url     : https://prove2.me/theorems/f95a1e40-577c-4813-a048-9dcdb6ad3f03
-- title:
--   Lemma A.3 — the three-level edge check from {−3 + a, b} is feasible iff (a, b) ≠ (1, 1) (explicit construction of the proof)
-- statement:
--   For $a, b \in \{0,1\}$ and the three-level construction of the proof (`checkData`: all coefficients $0$; sorted leaf intervals level 1: $[-3,-2],[1,2]$; level 2: $[-2,-1],[1,2]$; level 3: $[-1,0],\{0\},[0,1],[1,2]$): a sequence from $\{-3+a, b\}$ with the prescribed leaf counts and intervals exists if and only if $(a,b) \ne (1,1)$; and for each permitted input it is unique, ends with no internal vertices and has score zero.
--
--   Source (p. 41): "Lemma A.3. For $a, b \in \{0,1\}$, there is a three-level construction starting from $\{-3+a, b\}$ and ending with no internal vertices that has a feasible sequence if and only if $(a,b) \ne (1,1)$. For each permitted input, the sequence of coordinate multisets is unique and has score zero."
--
--   Differences from the source:
--   - generalization: there is a three-level construction → the explicit construction of the proof (p. 41), checkData; reason: the explicit data implies the existential and is what Lemma 3.2's proof uses
--   - encoding: ending with no internal vertices → conclusion X_3 = ∅ for the feasible sequence; reason: forced by the leaf counts (2, 2, 4) from two starting vertices
--   - encoding: feasible sequence of coordinate multisets → X : Fin 4 → Multiset ℤ with the prescribed counts and intervals (IsFeasibleSeq); reason: coordinates are integers
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 41, Lemma A.3 (construction from its proof)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Gadgets

namespace UnequalHuffman.NPC

open LeafData

/-- Lemma A.3 (p. 41), for the three-level edge-check construction of its proof (`checkData`):
for `a, b ∈ {0, 1}`, a sequence from `{-3 + a, b}` with the prescribed leaf counts and intervals
exists iff `(a, b) ≠ (1, 1)`; for each permitted input it is unique, ends with no internal
vertices, and has score zero. -/
theorem lemma_A_3 (a b : ℤ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    ((∃ X : Fin (checkData.length + 1) → Multiset ℤ, checkData.IsFeasibleSeq {-3 + a, b} X) ↔
      ¬ (a = 1 ∧ b = 1)) ∧
    (¬ (a = 1 ∧ b = 1) →
      ∃ X : Fin (checkData.length + 1) → Multiset ℤ,
        checkData.IsFeasibleSeq {-3 + a, b} X ∧ X (Fin.last _) = 0 ∧ checkData.score X = 0 ∧
        ∀ Y : Fin (checkData.length + 1) → Multiset ℤ,
          checkData.IsFeasibleSeq {-3 + a, b} Y → Y = X) := by sorry

end UnequalHuffman.NPC
