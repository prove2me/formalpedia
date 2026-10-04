-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_program_correct
-- name    : ResourceScheduling.Graph.word_program_correct
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:58.227975+00:00
-- url     : https://prove2.me/theorems/e084fda7-18e6-4978-b20d-7cce4480b092
-- title:
--   word program correct
-- statement:
--   The total word program equals the original reduceWord on valid and malformed inputs.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
open CookPvsNP
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_program_correct : wordProgram = reduceWord := by sorry
end ResourceScheduling.Graph
