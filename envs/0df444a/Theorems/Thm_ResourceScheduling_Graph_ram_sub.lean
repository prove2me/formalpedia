-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_sub
-- name    : ResourceScheduling.Graph.ram_sub
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:54:43.954982+00:00
-- url     : https://prove2.me/theorems/69695b60-6df4-49ff-b1ab-8113d558baf3
-- title:
--   ram sub
-- statement:
--   Copied-register simultaneous consumption implements truncated natural subtraction with an explicit linear source-step bound.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_sub {V : Type} [DecidableEq V] (i j dst : V) :
    StackImplements RAMRep (ramSub i j dst)
      (fun s => s.set dst (s.val i - s.val j))
      (fun s => 9 * s.val i + 9 * s.val j + 3 * s.val dst + 13) := by sorry
end ResourceScheduling.Graph
