-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_emit_pair
-- name    : ResourceScheduling.Graph.emit_pair
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:57.561994+00:00
-- url     : https://prove2.me/theorems/fc08fc3f-b239-4e2d-bf97-bb038f84a57d
-- title:
--   emit pair
-- statement:
--   The conditional non-edge body emits exactly one canonical resource row when the pair qualifies, preserves prior output, and keeps numeric registers bounded.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem emit_pair (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n = N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (ifNonEdge (forN c2 k (by decide) emitCell)) B s ∧
    ((ifNonEdge (forN c2 k (by decide) emitCell)).eval s).out =
      (if s.val i < s.val j ∧ s.word.getD (s.val i * N + s.val j) Letter.sep ≠ Letter.one
        then ((List.range N).flatMap fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0))
        else []).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
