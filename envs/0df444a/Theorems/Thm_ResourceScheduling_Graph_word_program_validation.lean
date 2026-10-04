-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_program_validation
-- name    : ResourceScheduling.Graph.word_program_validation
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:25.840986+00:00
-- url     : https://prove2.me/theorems/5a937a4c-a261-42ab-a56f-cbaf2f7d8a89
-- title:
--   word program validation
-- statement:
--   The Boolean natural-index validator recognizes exactly the decoded adjacency-matrix conditions.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
open CookPvsNP
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_program_validation (n : ℕ) (bits : List Letter) :
    checkGraphBody n bits = true ↔ ValidGraphBody n bits := by sorry
end ResourceScheduling.Graph
