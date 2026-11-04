-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_rightPrefix_step
-- name    : ThreeSum.ReportingHostMasks.rightPrefix_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:47.362197+00:00
-- url     : https://prove2.me/theorems/445256b0-9a86-4cf6-971a-9782095f413f
-- title:
--   Reporting Host Masks: right Prefix step
-- statement:
--   The Reporting Host Masks construction uses the right Prefix step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L136-L148
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L136-L148

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.rightPrefix_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S) =
      rightPrefix k Q u ∪ blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by sorry
