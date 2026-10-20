-- Prove2me | Theorems.Thm_PermanentRollout_sourceSlicedGradientLinearInput_polynomial
-- name    : PermanentRollout.sourceSlicedGradientLinearInput_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/a31f62ab-a389-4f04-8f09-5ae9692a8d11
-- title:
--   PermanentRollout.sourceSlicedGradientLinearInput_polynomial
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

theorem PermanentRollout.sourceSlicedGradientLinearInput_polynomial {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (j : Fin m) :
    (sourceSlicedGradientLinearInput W j).polynomial =
      linearCoordinatePolynomial W j := by sorry
