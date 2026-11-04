-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_label_covers
-- name    : ThreeSum.BandRawA.label_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:04.851047+00:00
-- url     : https://prove2.me/theorems/da7235a4-90dd-4ae5-a190-b27edc697dce
-- title:
--   Band Raw A: label covers
-- statement:
--   The Band Raw A construction uses the label covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L150-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L150-L155

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.label_covers {n g s p : ℕ} {rs : List Record}
    (hs : s < rs.length) (hf : (rs.getD s default).flag=1)
    (hp : start g (rs.getD s default).a ≤ p)
    (he : p < stop n g (rs.getD s default).a) :
    (⟨s,p⟩ : Label) ∈ items n g rs := by sorry
