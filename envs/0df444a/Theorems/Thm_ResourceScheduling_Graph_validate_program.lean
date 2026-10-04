-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_validate_program
-- name    : ResourceScheduling.Graph.validate_program
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T16:00:45.294987+00:00
-- url     : https://prove2.me/theorems/5645a7fc-31dd-4428-b256-3083aae05a0e
-- title:
--   validate program
-- statement:
--   The complete matrix validation program preserves the numeric bound and retains its initial validity flag exactly when every diagonal and symmetry test succeeds.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem validate_program (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe validate B s ∧ (validate.eval s).val good =
      if ∀ i < N, s.word.getD (i * N + i) Letter.sep ≠ Letter.one ∧
        ∀ j < N, s.word.getD (i * N + j) Letter.sep = Letter.one →
          s.word.getD (j * N + i) Letter.sep = Letter.one then s.val good else 0 := by sorry
end ResourceScheduling.Graph
