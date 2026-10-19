-- Prove2me | Theorems.Thm_PermanentRollout_flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
-- name    : PermanentRollout.flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/b4a69252-2fe1-4135-adb0-590d596964a7
-- title:
--   PermanentRollout.flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
    (b t s d : ℕ) (tree : BlockTree (Fin b)) :
    MvPolynomial.rename
        (finProdFinEquiv :
          Fin (b * t) × Fin s ≃ Fin ((b * t) * s))
        (sourceTreeSeparatedMinorSum b t s d tree) =
      flattenedSeparatedBlockMinorSum b t s d
        (sourceTreeBlockWeight b d tree) := by sorry
