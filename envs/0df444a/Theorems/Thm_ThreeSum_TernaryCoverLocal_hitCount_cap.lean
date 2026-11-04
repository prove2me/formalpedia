-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_hitCount_cap
-- name    : ThreeSum.TernaryCoverLocal.hitCount_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:16.149449+00:00
-- url     : https://prove2.me/theorems/d461984b-2ecc-469d-94da-779364f06fda
-- title:
--   Ternary Cover Local: hit Count cap
-- statement:
--   The retained fiber cap is obtained from actual light endpoint buckets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L153-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L153-L176

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]

theorem ThreeSum.TernaryCoverLocal.hitCount_cap (α π : DigitType) (B : ℕ)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) (hp : 2 < p) :
    hitCount α π B w a b ≤ B ^ 2 := by sorry
