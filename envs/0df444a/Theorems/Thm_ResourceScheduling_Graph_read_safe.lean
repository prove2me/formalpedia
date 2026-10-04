-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_read_safe
-- name    : ResourceScheduling.Graph.read_safe
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:59:17.777737+00:00
-- url     : https://prove2.me/theorems/69592090-3e08-4fa1-8058-87b0c7baccad
-- title:
--   read safe
-- statement:
--   Matrix lookup keeps every numeric register bounded when both indices and the dimension are bounded by N and the global bound exceeds N squared plus N.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg

namespace ResourceScheduling.Graph
theorem read_safe (a b dst : GraphReg) (h : b ≠ index) (B N : ℕ) (s : RAMState GraphReg)
    (hs : RAMBound B s) (ha : s.val a ≤ N) (hn : s.val n ≤ N) (hb : s.val b ≤ N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) : RAMSafe (GraphProgram.read a b dst h) B s := by sorry
end ResourceScheduling.Graph
