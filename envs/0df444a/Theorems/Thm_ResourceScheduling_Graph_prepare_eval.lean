-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_prepare_eval
-- name    : ResourceScheduling.Graph.prepare_eval
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:52.844975+00:00
-- url     : https://prove2.me/theorems/959a702c-8bc7-4d30-b62c-f1aa4d726a5c
-- title:
--   prepare eval
-- statement:
--   Unary parsing and the two length comparisons set the parameter, dimension, remaining word, and validity flag exactly as specified.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem prepare_eval (s : RAMState GraphReg) :
    (prepare.eval s).val t = (splitOnes s.word).1 ∧
    (prepare.eval s).val n = 3 * (splitOnes s.word).1 ∧
    (prepare.eval s).word = (splitOnes s.word).2.tail ∧
    (prepare.eval s).out = s.out ∧
    (prepare.eval s).val good =
      if (splitOnes s.word).2 ≠ [] ∧ (splitOnes s.word).2.tail.length =
        (3 * (splitOnes s.word).1) * (3 * (splitOnes s.word).1) then 1 else 0 := by sorry
end ResourceScheduling.Graph
