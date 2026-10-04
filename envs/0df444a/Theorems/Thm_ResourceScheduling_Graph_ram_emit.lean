-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_emit
-- name    : ResourceScheduling.Graph.ram_emit
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:37:14.639751+00:00
-- url     : https://prove2.me/theorems/9e553996-92ee-4450-8ca7-5fda6860719d
-- title:
--   ram emit
-- statement:
--   Register emission prepends precisely the reversed unary field and has a linear source-step bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMOps
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_emit {V : Type} [DecidableEq V] (v : V) :
    StackImplements RAMRep (ramEmit v)
      (fun s => { s with out := Letter.sep :: (List.replicate (s.val v) Letter.one ++ s.out) })
      (fun s => 9 * s.val v + 7) := by sorry
end ResourceScheduling.Graph
