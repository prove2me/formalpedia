-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_read_bit
-- name    : ResourceScheduling.Graph.ram_read_bit
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:37:28.241966+00:00
-- url     : https://prove2.me/theorems/4e5bc098-3a04-4a89-a7f1-64ab2d6d1d87
-- title:
--   ram read bit
-- statement:
--   Adjacency lookup sets a register to one exactly when the indexed input symbol is one, preserves scratch, and has a linear source-and-index budget.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMOps
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_read_bit {V : Type} [DecidableEq V] (i dst : V) :
    StackImplements RAMRep (ramReadBit i dst)
      (fun s => s.set dst (if s.word.getD (s.val i) Letter.sep = Letter.one then 1 else 0))
      (fun s => 9 * s.word.length + 9 * s.val i + 3 * s.val dst + 17) := by sorry
end ResourceScheduling.Graph
