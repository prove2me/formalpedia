-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_program_run
-- name    : ResourceScheduling.Graph.program_run
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:01:50.379997+00:00
-- url     : https://prove2.me/theorems/18af01ad-86ab-4dd6-9c11-231601baeaf8
-- title:
--   program run
-- statement:
--   The entire fixed register program produces exactly the total word-program output in reversed storage and executes within the stated quadratic bound on every numeric register and input suffix.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem program_run (B L : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hL : s.word.length ≤ L) (hB : 9 * L * L + 3 * L + 2 ≤ B) :
    RAMSafe program B s ∧ (program.eval s).out = (wordProgram s.word).reverse ++ s.out := by sorry
end ResourceScheduling.Graph
