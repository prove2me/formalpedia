-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_emit_row
-- name    : ResourceScheduling.Graph.emit_row
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:01:11.482902+00:00
-- url     : https://prove2.me/theorems/f3e01100-9627-4c26-bf38-004aa5ad77c4
-- title:
--   emit row
-- statement:
--   The middle emission loop visits the qualifying columns in order and emits their exact resource rows with a uniform numeric bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem emit_row (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell))) B s ∧
    ((forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell))).eval s).out =
      (((List.range N).filter fun j => decide (s.val i < j ∧
        s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)).flatMap fun j =>
          (List.range N).flatMap fun k => unary (if k = s.val i ∨ k = j then 1 else 0)).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
