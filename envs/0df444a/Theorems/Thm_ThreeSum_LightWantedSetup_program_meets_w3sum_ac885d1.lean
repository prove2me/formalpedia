-- Prove2me | Theorems.Thm_ThreeSum_LightWantedSetup_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWantedSetup.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:28:57.809053+00:00
-- url     : https://prove2.me/theorems/acc47758-949f-44c9-9706-48c7b7573341
-- title:
--   Light Wanted Setup: program meets
-- statement:
--   The Light Wanted Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L76-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWantedSetup.lean#L76-L192

import Definitions.Def_Submission_ThreeSum_LightWantedJoin
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightWantedSetup
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

set_option autoImplicit false
open ThreeSum ThreeSum.LightWantedSetup
open Light WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits}

theorem ThreeSum.LightWantedSetup.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {a b NL NR M free U D d : ℕ} {shift : ℤ}
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : space free M left right NL NR U D shift ≤ lim.space)
    (hword : (LightSourceResidues.word M M U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+5 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 11 d [a,b,NL,NR,M,shift,free] μ (time M left right NL NR U D shift)
      (fun r ν => r=(free : ℤ) ∧ Output ν free M left right NL NR shift ∧ Kept μ ν free) := by sorry
