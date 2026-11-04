-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
-- name    : ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:20:36.705706+00:00
-- url     : https://prove2.me/theorems/38a55461-8787-413d-b5e0-946ffcaad970
-- title:
--   Light Weighted Source Count Host: source Args length
-- statement:
--   The Light Weighted Source Count Host construction uses the source Args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L52-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L52-L53

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.sourceArgs_length (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := by sorry

attribute [defeq] ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
