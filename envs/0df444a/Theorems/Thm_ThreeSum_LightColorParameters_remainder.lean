-- Prove2me | Theorems.Thm_ThreeSum_LightColorParameters_remainder
-- name    : ThreeSum.LightColorParameters.remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:04.372278+00:00
-- url     : https://prove2.me/theorems/f0132af2-4438-428c-923c-f3c3c0a48ac6
-- title:
--   Light Color Parameters: remainder
-- statement:
--   The Light Color Parameters construction uses the remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorParameters.lean#L43-L47

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Submission_ThreeSum_LightColorParameters
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorParameters
open Light ColorParameters
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

theorem ThreeSum.LightColorParameters.remainder (a b : ℕ) :
    (a : ℤ)-((a/b : ℕ) : ℤ)*(b : ℤ)=((a%b : ℕ) : ℤ) := by sorry
