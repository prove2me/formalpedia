-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_emit_header
-- name    : ResourceScheduling.Graph.emit_header
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:01:36.654682+00:00
-- url     : https://prove2.me/theorems/9226d9dc-28c7-47c3-9b47-3e0760d206ef
-- title:
--   emit header
-- statement:
--   The emission prefix writes the two speeds, dimension, and resource count as exact unary fields while keeping numeric registers bounded.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem emit_header (B : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s) (hB : 2 ≤ B) :
    let p := block [.zero num, .inc num, .inc num, .emit num,
      .zero num, .inc num, .emit num, .emit n, .emit count]
    RAMSafe p B s ∧ p.eval s =
      { s.set num 1 with out :=
        (unary 2 ++ unary 1 ++ unary (s.val n) ++ unary (s.val count)).reverse ++ s.out } := by sorry
end ResourceScheduling.Graph
