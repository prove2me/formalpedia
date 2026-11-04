-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_factorial_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.factorial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:09:35.466201+00:00
-- url     : https://prove2.me/theorems/26aaa668-d492-44a5-bd6a-9c9b4e95f863
-- title:
--   Weighted Global Native Moment Bounds: factorial le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the factorial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L52-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L52-L62

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.factorial_le {N : ℕ} (Q : TritWord N) : TernaryConvolution.factorial Q≤(2 : ℤ)^N := by sorry
