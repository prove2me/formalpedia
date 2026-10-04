-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_count_program
-- name    : ResourceScheduling.Graph.count_program
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:48.782149+00:00
-- url     : https://prove2.me/theorems/c3f02523-a31c-4b57-bf96-f009482dbd8a
-- title:
--   count program
-- statement:
--   The complete nested counting program computes the exact length of the ordered non-edge list and preserves the uniform numeric bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem count_program (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N + 1 ≤ B) :
    RAMSafe countEdges B s ∧ (countEdges.eval s).val count = (wordNonEdges N s.word).length := by sorry
end ResourceScheduling.Graph
