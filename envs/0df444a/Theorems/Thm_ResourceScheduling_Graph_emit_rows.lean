-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_emit_rows
-- name    : ResourceScheduling.Graph.emit_rows
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:56.539039+00:00
-- url     : https://prove2.me/theorems/7482f07f-e676-426a-b062-9a50ac603d84
-- title:
--   emit rows
-- statement:
--   The complete nested emission loops produce the exact ordered resource matrix in reversed storage and preserve the uniform numeric bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem emit_rows (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe emitRows B s ∧ (emitRows.eval s).out =
      ((wordNonEdges N s.word).flatMap fun p => (List.range N).flatMap fun k =>
        unary (if k = p.1 ∨ k = p.2 then 1 else 0)).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
