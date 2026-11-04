-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets_with_masks_w3sum_ac885d1
-- name    : ThreeSum.LightGlobalKeys.Procs.meets_with_masks_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:19.101116+00:00
-- url     : https://prove2.me/theorems/dae90ee1-673b-40ae-874f-4ea761b74f74
-- title:
--   Procs: meets with masks
-- statement:
--   The Procs construction uses the meets with masks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalKeys.lean#L90-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalKeys.lean#L90-L183

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalKeys.Procs.meets_with_masks_w3sum_ac885d1 {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+5 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ free)
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,2*h,scheduleSize h,localPrime h,J,maps,
      outputCount (512*h) h,free] μ (time h J)
      (fun r ν => r=((scratch free h+LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
        ν (scratch free h+LightRadixKeys.offset (localCount h) J)=((localCount h^J : ℕ) : ℤ) ∧
        Seg ν (scratch free h+LightRadixKeys.offset (localCount h) J+1) (globalKeys h J) ∧
        (∀ i < outputCount (512*h) h,
          ν (free+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧
        Kept μ ν free) := by sorry
