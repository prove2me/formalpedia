-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_validate_inner
-- name    : ResourceScheduling.Graph.validate_inner
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:59:52.981447+00:00
-- url     : https://prove2.me/theorems/ddb022fe-afb2-44d6-b74b-69c7c7d3ffc4
-- title:
--   validate inner
-- statement:
--   The inner validation loop tests symmetry for every column in order and leaves the validity flag set exactly when every test succeeds.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem validate_inner (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) validateCell) B s ∧
    ((forN c1 j (by decide) validateCell).eval s).val good =
      if ∀ j < N, s.word.getD (s.val i * N + j) Letter.sep = Letter.one →
        s.word.getD (j * N + s.val i) Letter.sep = Letter.one then s.val good else 0 := by sorry
end ResourceScheduling.Graph
