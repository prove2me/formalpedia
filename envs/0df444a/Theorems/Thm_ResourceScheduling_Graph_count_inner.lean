-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_count_inner
-- name    : ResourceScheduling.Graph.count_inner
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:36.819901+00:00
-- url     : https://prove2.me/theorems/29bcd815-3338-4689-b034-d0b92155edb9
-- title:
--   count inner
-- statement:
--   The inner non-edge counting loop counts exactly the qualifying columns in increasing order while preserving the numeric bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem count_inner (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hc : s.val count + N + 1 ≤ B)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) (ifNonEdge (.inc count))) B s ∧
    ((forN c1 j (by decide) (ifNonEdge (.inc count))).eval s).val count = s.val count +
      ((List.range N).filter fun j => decide (s.val i < j ∧
        s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)).length := by sorry
end ResourceScheduling.Graph
