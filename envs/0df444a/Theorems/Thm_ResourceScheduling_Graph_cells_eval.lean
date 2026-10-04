-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_cells_eval
-- name    : ResourceScheduling.Graph.cells_eval
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:58:02.161+00:00
-- url     : https://prove2.me/theorems/276d7378-7644-40ea-a3ff-2efa23b04c5d
-- title:
--   cells eval
-- statement:
--   The elementary validation, non-edge count, and resource-cell emission operations have exactly their intended graph semantics.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
open ResourceScheduling.Graph GraphReg

namespace ResourceScheduling.Graph
theorem cells_eval (s : RAMState GraphReg) :
    (GraphProgram.validateCell.eval s).val good =
      (if s.word.getD (s.val i * s.val n + s.val j) Letter.sep = Letter.one ∧
        s.word.getD (s.val j * s.val n + s.val i) Letter.sep ≠ Letter.one then 0 else s.val good) ∧
    ((GraphProgram.ifNonEdge (.inc count)).eval s).val count = s.val count +
      (if s.val i < s.val j ∧ s.word.getD (s.val i * s.val n + s.val j) Letter.sep ≠ Letter.one
        then 1 else 0) ∧
    (GraphProgram.emitCell.eval s).out =
      (unary (if s.val k = s.val i ∨ s.val k = s.val j then 1 else 0)).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
