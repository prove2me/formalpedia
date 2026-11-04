-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeys_Procs_meets_with_masks_w3sum_ac885d1
-- name    : ThreeSum.LightCoverKeys.Procs.meets_with_masks_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:49:07.20308+00:00
-- url     : https://prove2.me/theorems/4c59f21b-976d-4bf4-968a-49661883a20f
-- title:
--   Procs: meets with masks
-- statement:
--   The Procs construction uses the meets with masks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeys.lean#L46-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeys.lean#L46-L132

import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_WeightedCache3SUM_Alias_188c0aebc110975b

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverKeys.Procs.meets_with_masks_w3sum_ac885d1 {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,J,free] μ (time h J)
      (fun r ν => r=(keyHeader free h J : ℤ) ∧
        ν (keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        Seg ν (keyHeader free h J+1) (globalKeys h J) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps (LightLocalCoverInit.base free) h)
          (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
          (matrixPtr (LightLocalCoverInit.base free) h) ∧
        ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (LightLocalCoverInit.base free) h+s.val)=
          (candidateAt h s : ℤ)) ∧
        (∀ i < outputCount (512*h) h, ν (afterCover free h+i)=
          (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧ Kept μ ν free) := by sorry
