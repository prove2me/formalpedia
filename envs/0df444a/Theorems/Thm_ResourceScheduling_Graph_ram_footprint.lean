-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_footprint
-- name    : ResourceScheduling.Graph.ram_footprint
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:23:10.601972+00:00
-- url     : https://prove2.me/theorems/9858c317-d1a1-4261-89c9-b624c8204c4b
-- title:
--   ram footprint
-- statement:
--   A structured register program preserves every register outside its syntactic write footprint, including across loops.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMCode
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_footprint {V : Type} [DecidableEq V] (p : RAMCode V) (v : V)
    (h : p.writes v = false) (s : RAMState V) : (p.eval s).val v = s.val v := by sorry
end ResourceScheduling.Graph
