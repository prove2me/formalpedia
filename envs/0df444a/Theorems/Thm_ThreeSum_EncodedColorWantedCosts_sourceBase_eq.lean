-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_eq
-- name    : ThreeSum.EncodedColorWantedCosts.sourceBase_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:46:51.738068+00:00
-- url     : https://prove2.me/theorems/c4a9f625-1e21-46c5-bb6f-bc8e59f6a50d
-- title:
--   Encoded Color Wanted Costs: source Base eq
-- statement:
--   The Encoded Color Wanted Costs construction uses the source Base eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L43-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L43-L49

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000

theorem ThreeSum.EncodedColorWantedCosts.sourceBase_eq (free M h J len : ℕ) :
    sourceBase free M h J len=LightCoverKeyData.keyEnd free h J+
      6*len+2*LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*LightGuardedWanted.totalKeys h J/M) := by sorry
