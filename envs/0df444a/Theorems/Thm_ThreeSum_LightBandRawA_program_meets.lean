-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawA_program_meets
-- name    : ThreeSum.LightBandRawA.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:53:27.998207+00:00
-- url     : https://prove2.me/theorems/3005fb7b-6e82-45f4-bec5-84fa15444dbf
-- title:
--   Light Band Raw A: program meets
-- statement:
--   The Light Band Raw A construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L171-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L171-L184

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawA.program_meets (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hg : 0 < g)
    (hrecords : records + 4 * rs.length ≤ vals) (hsrc : src + n ≤ vals) (hspace : space vals rs.length g ≤ lim.space)
    (hword : (word n g rs.length : ℤ) ≤ lim.word)
    (hvalid : ∀ i < rs.length, (rs.getD i default).flag = 1 → (rs.getD i default).a < BandPartition.size n g)
    (hrecordRead : Seg μ records (cells rs)) (hread : ∀ j < n, μ (src + j) = f j) :
    Meets lim program 0 d [records, rs.length, src, n, g, vals] μ (time rs.length g)
      (fun r ν =>
        r = ((items n g rs).length : ℤ) ∧
          Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g) f (items n g rs) ∧
            Kept μ ν vals) := by sorry
