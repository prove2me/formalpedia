-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_le_idealOfVars
-- name    : PermanentRollout.homogeneousLinearSliceIdeal_le_idealOfVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/a5452272-989a-4ed4-970c-72df544f878a
-- title:
--   PermanentRollout.homogeneousLinearSliceIdeal_le_idealOfVars
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

theorem PermanentRollout.homogeneousLinearSliceIdeal_le_idealOfVars
    {t n : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hproper : I ≠ ⊤) (c : Fin n → Fin t → ℂ) :
    homogeneousLinearSliceIdeal I c ≤
      MvPolynomial.idealOfVars (Fin t) ℂ := by sorry
