-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_suppression
-- name    : UnequalHuffman.NPC.suppression
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:34.015729+00:00
-- url     : https://prove2.me/theorems/66cc8af1-1e5f-424e-a085-bc50a5f11c46
-- title:
--   §2.1 (suppression) — optimal binary prefix codes are full
-- statement:
--   Let $w_1,\dots,w_N \ge 1$ be frequencies with $N \ge 2$ and let $c_0, c_1 \ge 1$ be letter costs. Then:
--
--   1. for every binary prefix code $C$ and every one-child vertex $v$ of its code tree (only child $va$), the suppressed code $C'$ (the letter $a$ at position $|v|$ deleted from every codeword beginning with $va$) is again a prefix code, and $L(C') < L(C)$ and $\mathrm{cost}_{c_0,c_1}(C') < \mathrm{cost}_{c_0,c_1}(C)$;
--   2. every prefix code that is not full is beaten by a full prefix code with strictly smaller weighted length and strictly smaller cost;
--   3. every cost-optimal prefix code is full, and every prefix code of minimum weighted length is full.
--
--   Source (p. 7): "With positive frequencies and letter costs, suppressing a vertex with only one child preserves the prefix property and strictly decreases both weighted length and coding cost. Repeating this operation produces a full code tree. Hence every optimal code is full, and every nonfull competitor can be improved to a full one."
--
--   Differences from the source:
--   - generalization: positive integer letter costs c0 < c1 (standing assumption, p. 4) → c0 ≥ 1 and c1 ≥ 1, no order between them; reason: the claim itself requires only positive letter costs; it specializes to c0 < c1
--   - reading: repeating suppression produces a full code tree; every nonfull competitor can be improved to a full one → clause 2: every nonfull prefix code has a full prefix code with strictly smaller weighted length and strictly smaller cost; reason: the end product of the repetition is what the text asserts and what pp. 33 and 35 use
--   - reading: every optimal code is full → both every cost-optimal and every length-optimal prefix code is full; reason: the sentence asserts the strict decrease for both objectives, and Lemma 4.1's proof uses it for both (p. 33)
--   - encoding: a binary prefix code and its code tree; suppressing a one-child vertex → C : Fin N → List Bool with IsInstantaneous; the code tree is the set of prefixes of codewords; suppress C v a deletes the letter at position |v| from every codeword beginning with v ++ [a]; reason: words over Bool, false = 0, true = 1
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 7, §2.1 (unnumbered claim)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Coding

open FuchsThesis.Coding

namespace UnequalHuffman.NPC

/-- §2.1 (p. 7): with positive frequencies and positive letter costs, suppressing a one-child
vertex of a prefix code keeps it a prefix code and strictly decreases both the weighted length and
the coding cost; every nonfull prefix code is beaten, in both objectives, by a full one; hence
every optimal code (for the coding cost, and for the weighted length) is full. -/
theorem suppression (w : List ℕ) (c0 c1 : ℕ) (hN : 2 ≤ w.length) (hw : ∀ x ∈ w, 1 ≤ x)
    (hc0 : 1 ≤ c0) (hc1 : 1 ≤ c1) :
    (∀ C : Fin w.length → List Bool, IsInstantaneous C →
      ∀ (v : List Bool) (a : Bool), IsOneChildVertex C v a →
        IsInstantaneous (suppress C v a) ∧
        weightedLength w (suppress C v a) < weightedLength w C ∧
        cost c0 c1 w (suppress C v a) < cost c0 c1 w C) ∧
    (∀ C : Fin w.length → List Bool, IsInstantaneous C → ¬ IsFullCode C →
      ∃ C' : Fin w.length → List Bool, IsInstantaneous C' ∧ IsFullCode C' ∧
        weightedLength w C' < weightedLength w C ∧ cost c0 c1 w C' < cost c0 c1 w C) ∧
    (∀ C : Fin w.length → List Bool, IsCostOptimal c0 c1 w C → IsFullCode C) ∧
    (∀ C : Fin w.length → List Bool, IsLengthOptimal w C → IsFullCode C) := by sorry

end UnequalHuffman.NPC
