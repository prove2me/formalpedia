-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_mem
-- name    : ThreeSum.ReportingHostMasks.globalChildren_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:34.815928+00:00
-- url     : https://prove2.me/theorems/c06c457c-cd05-4aab-add7-32335e4b8eb6
-- title:
--   Reporting Host Masks: global Children mem
-- statement:
--   The Reporting Host Masks construction uses the global Children mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L78-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L78-L80

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.globalChildren_mem {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    blockSet i S ∈ globalChildren i Q h ↔ S ⊆ Q ∧ S.card = h := by sorry
