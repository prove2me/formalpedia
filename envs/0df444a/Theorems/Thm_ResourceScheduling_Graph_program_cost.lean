-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_program_cost
-- name    : ResourceScheduling.Graph.program_cost
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:01:29.193891+00:00
-- url     : https://prove2.me/theorems/a6247008-71bf-409d-9e4b-a8c0926b04d5
-- title:
--   program cost
-- statement:
--   The actual fixed graph program and the final reversal transfer fit one polynomial source-step deadline on every word, including empty and malformed inputs.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem program_cost : ∃ k, ∀ w : List Letter,
    program.cost ⟨fun _ => 0, w, []⟩ + 3 * (wordProgram w).length + 2 ≤ w.length ^ k + k := by sorry
end ResourceScheduling.Graph
