-- Prove2me | Theorems.Thm_PermanentRollout_flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
-- name    : PermanentRollout.flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/24adb40a-53eb-4003-aee2-c3a12421c7d8
-- title:
--   PermanentRollout.flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
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

theorem PermanentRollout.flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
    {b t s d : ℕ} (hd : 3 ≤ d)
    (weight : Fin b → ℂ) (hw : ∀ h, weight h ≠ 0)
    (hincidence :
      ringKrullDim (BlockIncidenceCoordinateRing b t s d) ≤
        ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞)) :
    criticalLocusDimension
      (flattenedSeparatedBlockMinorSum b t s d weight) ≤
        ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by sorry
