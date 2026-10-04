-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_stack_emit
-- name    : ResourceScheduling.Graph.stack_emit
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:16:24.377771+00:00
-- url     : https://prove2.me/theorems/5d003ab2-0160-482e-bffc-05219bbaa8cb
-- title:
--   stack emit
-- statement:
--   Unary field emission preserves the source register and scratch, prepends the reversed canonical field, and costs nine times the source length plus seven.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_StackEmit
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem stack_emit {K : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List Letter) (h2 : s (r 2) = []) (h3 : s (r 3) = []) :
    (emitUnaryProg r).Exec s
      (Function.update s (r 1) (Letter.sep :: (List.replicate (s (r 0)).length Letter.one ++ s (r 1))))
      (9 * (s (r 0)).length + 7) := by sorry
end ResourceScheduling.Graph
