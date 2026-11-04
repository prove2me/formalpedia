-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_source_eq_left
-- name    : ThreeSum.LightBlockSourceRetainedStages.source_eq_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:23:50.141059+00:00
-- url     : https://prove2.me/theorems/333197fe-c7b6-4a79-a109-aa91dad10237
-- title:
--   Light Block Source Retained Stages: source eq left
-- statement:
--   The Light Block Source Retained Stages construction uses the source eq left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L26-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L26-L36

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_left

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000

theorem ThreeSum.LightBlockSourceRetainedStages.source_eq_left {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) 0 v N) = BlockIndexedQuery.leftSource (p : ℤ) B b q := by sorry
