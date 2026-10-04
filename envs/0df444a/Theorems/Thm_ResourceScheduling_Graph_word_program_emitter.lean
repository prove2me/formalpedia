-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_word_program_emitter
-- name    : ResourceScheduling.Graph.word_program_emitter
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:46.74187+00:00
-- url     : https://prove2.me/theorems/0108df5e-f0bb-4efc-b8c0-69d7107ba300
-- title:
--   word program emitter
-- statement:
--   The natural-index emitter is exactly the original scheduling-instance unary encoding.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_WordProgram
open CookPvsNP
open ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem word_program_emitter (t : ℕ) (bits : List Letter) (G : SimpleGraph (Fin (3 * t)))
    [DecidableRel G.Adj]
    (h : ∀ i j : Fin (3 * t), G.Adj i j ↔
      bits.getD (i.val * (3 * t) + j.val) Letter.sep = Letter.one) :
    emitQ2Word t bits = encQ2 (![2, 1], construct G t) := by sorry
end ResourceScheduling.Graph
