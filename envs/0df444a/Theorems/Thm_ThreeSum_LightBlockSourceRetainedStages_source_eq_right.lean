-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_source_eq_right
-- name    : ThreeSum.LightBlockSourceRetainedStages.source_eq_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:24:28.148215+00:00
-- url     : https://prove2.me/theorems/62128ee9-82a2-450b-8a5e-55896b21b96a
-- title:
--   Light Block Source Retained Stages: source eq right
-- statement:
--   The Light Block Source Retained Stages construction uses the source eq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L38-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L38-L49

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_right

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000

theorem ThreeSum.LightBlockSourceRetainedStages.source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (shift : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) shift v N) =
      BlockIndexedQuery.rightSource (p : ℤ) shift B b q := by sorry
