-- Prove2me | Theorems.Thm_ThreeSum_LocalKeyArraySemantics_localKeys_eq_flatMap
-- name    : ThreeSum.LocalKeyArraySemantics.localKeys_eq_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:04.239198+00:00
-- url     : https://prove2.me/theorems/ee462944-6459-4575-bcc4-8fa06a3d8c1d
-- title:
--   Local Key Array Semantics: local Keys eq flat Map
-- statement:
--   The Local Key Array Semantics construction uses the local Keys eq flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalKeyArraySemantics.lean#L41-L45

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
set_option autoImplicit false
open ThreeSum ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LocalKeyArraySemantics.localKeys_eq_flatMap (h : ℕ) :
    localKeys h = (List.finRange (scheduleSize h)).flatMap
      (fun o => List.ofFn (fun i => blockKey (o,layerRecord h i))) := by sorry
