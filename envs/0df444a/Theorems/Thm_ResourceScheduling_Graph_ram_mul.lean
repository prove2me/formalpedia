-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_ram_mul
-- name    : ResourceScheduling.Graph.ram_mul
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:54:44.296546+00:00
-- url     : https://prove2.me/theorems/e94c8a03-6136-4db5-b902-29f4539df694
-- title:
--   ram mul
-- statement:
--   Repeated copying implements natural multiplication with an explicit bilinear source-step bound and restores scratch.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMArithmetic
open CookPvsNP ResourceScheduling.Graph

namespace ResourceScheduling.Graph
theorem ram_mul {V : Type} [DecidableEq V] (i j dst : V) (h : j ≠ dst) :
    StackImplements RAMRep (ramMul i j dst h)
      (fun s => s.set dst (s.val i * s.val j))
      (fun s => (6 * s.val j + 13) * s.val i + 3 * s.val dst + 7) := by sorry
end ResourceScheduling.Graph
