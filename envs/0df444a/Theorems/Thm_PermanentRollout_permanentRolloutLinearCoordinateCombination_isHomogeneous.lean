-- Prove2me | Theorems.Thm_PermanentRollout_permanentRolloutLinearCoordinateCombination_isHomogeneous
-- name    : PermanentRollout.permanentRolloutLinearCoordinateCombination_isHomogeneous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/a2770f38-9eb0-4dda-977c-3b51ff45e003
-- title:
--   PermanentRollout.permanentRolloutLinearCoordinateCombination_isHomogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.permanentRolloutLinearCoordinateCombination_isHomogeneous
    {t : ℕ} (c : Fin t → ℂ) :
    (permanentRolloutLinearCoordinateCombination t c).IsHomogeneous 1 := by sorry
