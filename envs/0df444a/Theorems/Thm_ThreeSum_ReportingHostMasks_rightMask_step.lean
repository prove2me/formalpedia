-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_rightMask_step
-- name    : ThreeSum.ReportingHostMasks.rightMask_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:03.869112+00:00
-- url     : https://prove2.me/theorems/3e244199-6e50-4389-869f-18471aa298f3
-- title:
--   Reporting Host Masks: right Mask step
-- statement:
--   The Reporting Host Masks construction uses the right Mask step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L157-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L157-L172

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.rightMask_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) (hS : S ⊆ Q ⟨k,hk⟩) :
    (subsetMask (rightPrefix k Q u) : ℤ)+
      ((subsetMask (blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩)) : ℤ)-(subsetMask (blockSet ⟨k,hk⟩ S) : ℤ)) =
      (subsetMask (rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S)) : ℤ) := by sorry
