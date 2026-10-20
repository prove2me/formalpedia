-- Prove2me | Theorems.Thm_PermanentRollout_ringKrullDim_le_of_isIntegral
-- name    : PermanentRollout.ringKrullDim_le_of_isIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/c441e4dc-7209-42db-a017-f58b402ab702
-- title:
--   PermanentRollout.ringKrullDim_le_of_isIntegral
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Ideal
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem PermanentRollout.ringKrullDim_le_of_isIntegral
    [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by sorry
