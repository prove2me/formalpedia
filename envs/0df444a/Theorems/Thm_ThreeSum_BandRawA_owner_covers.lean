-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_owner_covers
-- name    : ThreeSum.BandRawA.owner_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:33.807919+00:00
-- url     : https://prove2.me/theorems/7912ff2d-0a7d-4deb-b6f0-f9b9b97bf6a4
-- title:
--   Band Raw A: owner covers
-- statement:
--   The Band Raw A construction uses the owner covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L157-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L157-L167

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandCandidateRows_owner_covers

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.owner_covers {A B C : Family} {n g p : ℕ} (t : Triple A B C)
    (ht : relevant A B C t) (hp : start g t.1.val ≤ p) (he : p < stop n g t.1.val) :
    (⟨slot A B C (owner A B C t),p⟩ : Label) ∈ items n g (records A B C) := by sorry
