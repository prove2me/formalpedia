-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_non_edge_safe
-- name    : ResourceScheduling.Graph.non_edge_safe
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:59:25.063775+00:00
-- url     : https://prove2.me/theorems/4d335f27-ec96-44c5-8747-9e110867a9a9
-- title:
--   non edge safe
-- statement:
--   The non-edge conditional preserves the numeric bound when its body does, including the intermediate subtraction and matrix read.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem non_edge_safe (p : Code) (B N : ℕ) (P : RAMState GraphReg → Prop)
    (hP : ∀ v ∈ [delta, index, bitA], ∀ s x, P s → P (s.set v x))
    (hp : ∀ s, RAMBound B s → P s → RAMSafe p B s)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hPs : P s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n ≤ N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) : RAMSafe (ifNonEdge p) B s := by sorry
end ResourceScheduling.Graph
