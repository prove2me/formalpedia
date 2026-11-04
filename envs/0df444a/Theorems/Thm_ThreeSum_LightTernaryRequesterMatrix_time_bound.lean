-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_time_bound
-- name    : ThreeSum.LightTernaryRequesterMatrix.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:10.663945+00:00
-- url     : https://prove2.me/theorems/316f2cae-8a0a-4372-827c-12fc057c2504
-- title:
--   Light Ternary Requester Matrix: time bound
-- statement:
--   The Light Ternary Requester Matrix construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L276-L286
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L276-L286

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_time_bound
import Theorems.Thm_ThreeSum_LightTernarySignedMatrix_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryRequesterMatrix.time_bound (n Q J U : ℕ) :
    time n Q J U≤1000*n*Q*(J+1)*(Nat.log 2 (3*U+1)+2)+230*n+30 := by sorry
