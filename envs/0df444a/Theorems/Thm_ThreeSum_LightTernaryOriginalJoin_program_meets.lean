-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
-- name    : ThreeSum.LightTernaryOriginalJoin.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:38:07.802177+00:00
-- url     : https://prove2.me/theorems/d1021cd0-5c1c-4e9e-bea3-bfa8fdc457d6
-- title:
--   Light Ternary Original Join: program meets
-- statement:
--   The Light Ternary Original Join construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L48-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L48-L73

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
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
open ThreeSum ThreeSum.LightTernaryOriginalJoin
open Light
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
variable {lim : Limits}

theorem ThreeSum.LightTernaryOriginalJoin.program_meets {μ : ℕ → ℤ} {src dict NL M free U D d J : ℕ}
    {p : ℤ} {base : List ℤ} {shift : ℤ} (input : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M)
    (hsrc : src+NL ≤ free) (hdict : dict+(keys p base J).length ≤ free)
    (hspace : LightWantedSetup.space free M input
      (fun j => (keys p base J).getD j 0) NL (keys p base J).length U D shift ≤ lim.space)
    (hword : (LightSourceResidues.word M M U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+5 ≤ lim.depth)
    (hinput : ∀ i < NL, μ (src+i)=input i)
    (hdictionary : Seg μ dict (keys p base J))
    (hvalues : ∀ i < NL, |input i| ≤ (U : ℤ))
    (hkeyBound : ∀ z ∈ keys p base J, |z| ≤ (U : ℤ)) :
    Meets lim program 11 d [src,dict,NL,(keys p base J).length,M,shift,free] μ
      (LightWantedSetup.time M input (fun j => (keys p base J).getD j 0)
        NL (keys p base J).length U D shift)
      (fun r ν => r=(free : ℤ) ∧
        LightWantedSetup.Output ν free M input
          (fun j => (keys p base J).getD j 0) NL (keys p base J).length shift ∧
        Kept μ ν free) := by sorry
