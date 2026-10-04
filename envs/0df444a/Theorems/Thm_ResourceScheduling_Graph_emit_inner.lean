-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_emit_inner
-- name    : ResourceScheduling.Graph.emit_inner
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:33.696167+00:00
-- url     : https://prove2.me/theorems/dba847f1-f58e-4576-86ce-65c6f0061c43
-- title:
--   emit inner
-- statement:
--   The innermost resource-row emission loop appends exactly the canonical unary resource fields to the reversed output while preserving the numeric bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem emit_inner (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hpos : 1 ≤ B) :
    RAMSafe (forN c2 k (by decide) emitCell) B s ∧
    ((forN c2 k (by decide) emitCell).eval s).out =
      ((List.range N).flatMap fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0)).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
