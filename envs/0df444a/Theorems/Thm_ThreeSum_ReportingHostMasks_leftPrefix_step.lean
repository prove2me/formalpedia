-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_leftPrefix_step
-- name    : ThreeSum.ReportingHostMasks.leftPrefix_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:33.765927+00:00
-- url     : https://prove2.me/theorems/58f11542-5b64-47f3-97c9-7baf6455ae5a
-- title:
--   Reporting Host Masks: left Prefix step
-- statement:
--   The Reporting Host Masks construction uses the left Prefix step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L112-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L112-L125

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.leftPrefix_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S) =
      leftPrefix k u ∪ blockSet ⟨k,hk⟩ S := by sorry
