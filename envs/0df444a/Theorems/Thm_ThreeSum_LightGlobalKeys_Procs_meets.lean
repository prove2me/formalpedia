-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets
-- name    : ThreeSum.LightGlobalKeys.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:00.920182+00:00
-- url     : https://prove2.me/theorems/5e8595fb-5e34-494d-a2be-852d70b3ad36
-- title:
--   Procs: meets
-- statement:
--   The original key-only API remains unchanged.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalKeys.lean#L186-L201
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalKeys.lean#L186-L201

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalKeys.Procs.meets {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
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
        Kept μ ν free) := by sorry
