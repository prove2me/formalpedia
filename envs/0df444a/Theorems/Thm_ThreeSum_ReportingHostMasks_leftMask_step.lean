-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_leftMask_step
-- name    : ThreeSum.ReportingHostMasks.leftMask_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:29.990416+00:00
-- url     : https://prove2.me/theorems/99c721ce-5236-4492-b6f1-264f9ff5a084
-- title:
--   Reporting Host Masks: left Mask step
-- statement:
--   The Reporting Host Masks construction uses the left Mask step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L150-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L150-L155

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.leftMask_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    (subsetMask (leftPrefix k u) : ℤ)+(subsetMask (blockSet ⟨k,hk⟩ S) : ℤ) =
      (subsetMask (leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S)) : ℤ) := by sorry
