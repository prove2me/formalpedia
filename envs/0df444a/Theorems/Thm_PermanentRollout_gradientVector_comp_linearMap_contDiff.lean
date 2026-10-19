-- Prove2me | Theorems.Thm_PermanentRollout_gradientVector_comp_linearMap_contDiff
-- name    : PermanentRollout.gradientVector_comp_linearMap_contDiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/67d16b09-456c-415a-9c1a-f71807f4a3b0
-- title:
--   PermanentRollout.gradientVector_comp_linearMap_contDiff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

theorem PermanentRollout.gradientVector_comp_linearMap_contDiff {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ContDiff ℝ 1 (fun u : Fin k → ℂ => gradientVector P (W u)) := by sorry
