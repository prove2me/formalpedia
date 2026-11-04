-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedWanted_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBalancedWanted.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:08.156029+00:00
-- url     : https://prove2.me/theorems/2b04da3d-1020-4cde-bccc-09a33ce26e0e
-- title:
--   Light Balanced Wanted: program meets
-- statement:
--   The Light Balanced Wanted construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L45-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedWanted.lean#L45-L101

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightBalancedWanted.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {a b NL NR M free U d : ℕ} [NeZero M]
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : space free M left right NL NR U ≤ lim.space)
    (hword : (word M NL NR U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 M+NL+6 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 25 d [a,b,NL,NR,M,free] μ (time M left right NL NR U)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M left right NL NR
          (LightOriginalOffset.selected M left right NL NR) ∧
        M*(ν free).toNat ≤ NL*NR ∧ Kept μ ν free) := by sorry
