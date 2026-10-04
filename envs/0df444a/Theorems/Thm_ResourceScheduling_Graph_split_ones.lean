-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_split_ones
-- name    : ResourceScheduling.Graph.split_ones
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:50:20.732596+00:00
-- url     : https://prove2.me/theorems/dd67f6ad-148b-4f38-a28e-9041afbcee49
-- title:
--   split ones
-- statement:
--   The leading-ones split reconstructs every input, gives a length identity, stops at a non-one, and agrees with readUnary including missing separators.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMParse
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem split_ones (w : List Letter) :
    w = List.replicate (splitOnes w).1 Letter.one ++ (splitOnes w).2 ∧
    (splitOnes w).2.head? ≠ some Letter.one ∧
    (splitOnes w).1 + (splitOnes w).2.length = w.length ∧
    readUnary w = if (splitOnes w).2 = [] then none
      else some ((splitOnes w).1, (splitOnes w).2.tail) := by sorry
end ResourceScheduling.Graph
