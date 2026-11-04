-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceCountHost_sourceArgs_length
-- name    : ThreeSum.LightTernarySourceCountHost.sourceArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:18:01.630611+00:00
-- url     : https://prove2.me/theorems/b4827df4-330e-4bb4-84e7-f71bea10c8da
-- title:
--   Light Ternary Source Count Host: source Args length
-- statement:
--   The Light Ternary Source Count Host construction uses the source Args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L47-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceCountHost.lean#L47-L48

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightTernarySourceCountHost.sourceArgs_length (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := by sorry

attribute [defeq] ThreeSum.LightTernarySourceCountHost.sourceArgs_length
