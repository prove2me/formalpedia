-- Prove2me | Theorems.Thm_PermanentRollout_leadingFormProjective_idealOfVars_isPrime
-- name    : PermanentRollout.leadingFormProjective_idealOfVars_isPrime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/da6d78f9-41fd-4b9a-b91c-576f1c985023
-- title:
--   PermanentRollout.leadingFormProjective_idealOfVars_isPrime
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

theorem PermanentRollout.leadingFormProjective_idealOfVars_isPrime (t : ℕ) :
    (MvPolynomial.idealOfVars (Fin t) ℂ).IsPrime := by sorry
