-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySignedMatrix_time_bound
-- name    : ThreeSum.LightTernarySignedMatrix.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:27.687991+00:00
-- url     : https://prove2.me/theorems/220ba0f5-66d9-40a3-a499-bf961c4c17ea
-- title:
--   Light Ternary Signed Matrix: time bound
-- statement:
--   The Light Ternary Signed Matrix construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L169-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySignedMatrix.lean#L169-L179

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySignedMatrix.time_bound (n J U : ℕ) :
    time n J U ≤ 600*n*(J+1)*(Nat.log 2 (3*U+1)+2)+20 := by sorry
