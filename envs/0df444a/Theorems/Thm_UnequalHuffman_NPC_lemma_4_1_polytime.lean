-- Prove2me | Theorems.Thm_UnequalHuffman_NPC_lemma_4_1_polytime
-- name    : UnequalHuffman.NPC.lemma_4_1_polytime
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:47:12.131497+00:00
-- url     : https://prove2.me/theorems/09ee7eb0-5e9b-4631-a13a-091bce95f96d
-- title:
--   Lemma 4.1 (polynomial-time clause; companion of lemma_4_1) — instance construction and both solution maps run in polynomial time
-- statement:
--   1. Some polynomial-time computable map sends the code of every well-formed leaf-profile instance $I$ to the binary code of $M$, $M+1$, the frequencies $w_1,\dots,w_N$ of (13) and the offset $\beta$ (so all constructed numbers have polynomial binary length).
--   2. (Forward solution map.) Some polynomial-time computable map sends the code of $I$ followed by any listing of the leaves of a feasible tree $T$ to the codeword list of a canonical code $C_T$.
--   3. (Reverse solution map.) Some polynomial-time computable map sends the code of $I$ followed by the codeword list of an optimal code $C$ of $J$ to a listing of the leaves of its code tree (the optimal source tree obtained by forgetting labels).
--
--   Source (pp. 32–33), last sentence of Lemma 4.1: "The instance construction and both solution maps take polynomial time, and all constructed numbers have polynomial binary encoding length."
--
--   Differences from the source:
--   - encoding: the instance construction and both solution maps take polynomial time → CookPvsNP.PolyTimeComputable maps on BSym strings: I.code ↦ outCode I; I.code ++ (leaf listing of T) ↦ codewords of a canonical C_T; I.code ++ (codewords of an optimal C) ↦ leaf listing of codeTree C; reason: the published polynomial-time notion; a tree is input and output as a listing of its leaves in any order
--   - encoding: all constructed numbers have polynomial binary encoding length → not a separate clause: outCode I (M, M + 1, w, β in binary) is the output of a polynomial-time map; reason: a Turing machine writes at most one symbol per step
--   - encoding: Lemma 4.1 as one statement → this item states only its polynomial-time clause; the other clauses are lemma_4_1; reason: length of the statement; both items are planned to be proved
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 32–33, Lemma 4.1 (last sentence)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_SecondReduction

open CookPvsNP FuchsThesis.Coding

namespace UnequalHuffman.NPC

open LPInstance

/-- Lemma 4.1 (pp. 32–33), polynomial-time clause (companion of `lemma_4_1`): the instance
construction (13) — the letter costs `M, M + 1`, the frequencies and the offset `β`, all in binary
— is polynomial-time computable from the code of a well-formed instance (so every constructed
number has polynomial binary length); the forward solution map, from any listing of the leaves of
a feasible tree `T` to a canonical code `C_T`, and the reverse map, from an optimal code to a
listing of the leaves of its tree, are polynomial-time computable. -/
theorem lemma_4_1_polytime :
    (∃ f : List ProjSchedTW.Complexity.BSym → List ProjSchedTW.Complexity.BSym,
      PolyTimeComputable f ∧ ∀ I : LPInstance, I.IsValid → f I.code = I.outCode) ∧
    (∃ g : List ProjSchedTW.Complexity.BSym → List ProjSchedTW.Complexity.BSym,
      PolyTimeComputable g ∧ ∀ I : LPInstance, I.IsValid → ∀ T : OTree, I.IsFeasibleTree T →
        ∀ ls : List (List Bool), ls.Nodup → ls.toFinset = T.leaves →
          ∃ C, I.IsCanonicalCode T C ∧ g (I.code ++ encWords ls) = encWords (List.ofFn C)) ∧
    (∃ h : List ProjSchedTW.Complexity.BSym → List ProjSchedTW.Complexity.BSym,
      PolyTimeComputable h ∧ ∀ I : LPInstance, I.IsValid →
        ∀ C : Fin I.freq.length → List Bool, IsCostOptimal I.bigM (I.bigM + 1) I.freq C →
          ∃ ls : List (List Bool), ls.Nodup ∧ ls.toFinset = (codeTree C).leaves ∧
            h (I.code ++ encWords (List.ofFn C)) = encWords ls) := by sorry

end UnequalHuffman.NPC
