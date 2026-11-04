-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverCapParameters_sourceCap_threshold
-- name    : ThreeSum.TernaryCoverCapParameters.sourceCap_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:30.072036+00:00
-- url     : https://prove2.me/theorems/23643f7f-998f-4a86-a549-8600c739be0d
-- title:
--   Ternary Cover Cap Parameters: source Cap threshold
-- statement:
--   The Ternary Cover Cap Parameters construction uses the source Cap threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L74-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L74-L78

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

theorem ThreeSum.TernaryCoverCapParameters.sourceCap_threshold (m p : ℕ) (hp : 0 < p) :
    8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ sourceCap m p*p := by sorry
