-- Prove2me | Theorems.Thm_ThreeSum_LightRawAKeys_program_meets
-- name    : ThreeSum.LightRawAKeys.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:04.366243+00:00
-- url     : https://prove2.me/theorems/862b2cd9-0242-4e1c-a514-6570525b70c4
-- title:
--   Light Raw AKeys: program meets
-- statement:
--   The Light Raw AKeys construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L116-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L116-L124

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
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
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRawAKeys.program_meets {src free p U : ℕ} {μ : ℕ → ℤ} (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (hsrc : src+xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space)
    (hword : (word p U : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,xs.length,p,free] μ (time xs.length U)
      (fun r ν => r=(free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) := by sorry
