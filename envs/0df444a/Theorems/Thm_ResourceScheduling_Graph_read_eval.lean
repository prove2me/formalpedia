-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_read_eval
-- name    : ResourceScheduling.Graph.read_eval
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:57:31.148232+00:00
-- url     : https://prove2.me/theorems/27afc874-776d-4ada-badb-cdda2c8b25a3
-- title:
--   read eval
-- statement:
--   The matrix-read macro computes row times dimension plus column, then reads exactly that ordinary input symbol.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
open ResourceScheduling.Graph GraphReg

namespace ResourceScheduling.Graph
theorem read_eval (a b dst : GraphReg) (h : b ≠ index) (s : RAMState GraphReg) :
    (GraphProgram.read a b dst h).eval s =
      let z := s.val a * s.val n + s.val b
      (s.set index z).set dst (if s.word.getD z Letter.sep = Letter.one then 1 else 0) := by sorry
end ResourceScheduling.Graph
