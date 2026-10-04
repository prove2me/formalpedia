-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_stack_prefix
-- name    : ResourceScheduling.Graph.stack_prefix
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:37:49.56624+00:00
-- url     : https://prove2.me/theorems/6d0805f2-d031-4be9-b1f2-2224651982d5
-- title:
--   stack prefix
-- statement:
--   A leading block of t ones is moved into the counter in exactly 3t+1 source steps, leaving its non-one suffix untouched.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_StackPrefix
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem stack_prefix {K : Type} [DecidableEq K] (input count : K) (hne : input ≠ count)
    (t : ℕ) (rest : List Letter) (hstop : rest.head? ≠ some .one)
    (s : K → List Letter) (hs : s input = List.replicate t .one ++ rest) :
    (prefixProg input count).Exec s
      (Function.update (Function.update s input rest) count (List.replicate t .one ++ s count))
      (3 * t + 1) := by sorry
end ResourceScheduling.Graph
