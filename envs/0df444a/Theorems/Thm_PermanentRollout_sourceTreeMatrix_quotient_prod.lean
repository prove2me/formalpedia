-- Prove2me | Theorems.Thm_PermanentRollout_sourceTreeMatrix_quotient_prod
-- name    : PermanentRollout.sourceTreeMatrix_quotient_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/dadea660-d547-46f2-a322-b050d6e59634
-- title:
--   PermanentRollout.sourceTreeMatrix_quotient_prod
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceTreeMatrix_quotient_prod
    (b t d : ℕ) (hd : d ≤ t) (ζ : ℂ)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    Ideal.Quotient.mk (squareZeroIdeal (b * t))
        (columnLinearFormProduct
          (sourceTreeMatrix b t d hd ζ tree hnodup hleaves)) =
      subtreeLinearFormProduct
        (fun h => squareZeroBlockSum (b * t) (sourceRowBlock b t h))
        t d ζ tree := by sorry
