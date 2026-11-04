-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_source_card_le
-- name    : ThreeSum.WeightedGlobalNativeMomentBounds.source_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:38.911109+00:00
-- url     : https://prove2.me/theorems/bf0d8977-8d8b-4177-9be2-cd7b248e4b0a
-- title:
--   Weighted Global Native Moment Bounds: source card le
-- statement:
--   The Weighted Global Native Moment Bounds construction uses the source card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L22-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeMomentBounds.lean#L22-L26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeMomentBounds
open Finset TernaryJointType WeightedGlobalNativePairMoments
open scoped BigOperators

theorem ThreeSum.WeightedGlobalNativeMomentBounds.source_card_le (S : TernarySourceExecutionFactory.Setup) :
    S.records.card≤S.NL*LightTernarySourceHost.size S.xs S.J := by sorry
