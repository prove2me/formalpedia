-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_flag
-- name    : ResourceScheduling.Graph.word_flag
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:50:20.951015+00:00
-- url     : https://prove2.me/theorems/b1070af1-d6b6-4642-b908-0768a50cdef2
-- title:
--   word flag
-- statement:
--   The parsed-length flag and complete matrix-validity condition select exactly the total word program output, including missing separators and malformed matrices.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
import Definitions.Def_ResourceScheduling_Graph_RAMParse
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_flag (w bits : List Letter) (N a g : ℕ)
    (hn : N = 3 * (splitOnes w).1) (hw : bits = (splitOnes w).2.tail)
    (ha : a = if (splitOnes w).2 ≠ [] ∧ bits.length = N * N then 1 else 0)
    (hg : g = if ∀ i < N, bits.getD (i * N + i) Letter.sep ≠ Letter.one ∧
      ∀ j < N, bits.getD (i * N + j) Letter.sep = Letter.one →
        bits.getD (j * N + i) Letter.sep = Letter.one then a else 0) :
    wordProgram w = if 0 < g then emitQ2Word (splitOnes w).1 (splitOnes w).2.tail else [] := by sorry
end ResourceScheduling.Graph
