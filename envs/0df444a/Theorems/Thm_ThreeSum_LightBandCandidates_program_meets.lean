-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
-- name    : ThreeSum.LightBandCandidates.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:53:09.073188+00:00
-- url     : https://prove2.me/theorems/375baf02-6759-4ac0-9208-67d2a9b38d47
-- title:
--   Light Band Candidates: program meets
-- statement:
--   The Light Band Candidates construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L189-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidates.lean#L189-L199

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_Submission_ThreeSum_LightBandCandidates
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
open ThreeSum ThreeSum.LightBandCandidates
open Light BandEnumeration BandCandidateRows
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst : ℕ}

theorem ThreeSum.LightBandCandidates.program_meets (A B C : Family) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 2 < lim.depth) (hsrc : src + LightBandEnumeration.count A.size B.size C.size ≤ dst)
    (hspace : space dst A.size B.size C.size ≤ lim.space) (hword : (word A.size B.size C.size : ℤ) ≤ lim.word)
    (htables : LightBandEnumeration.Tables μ src A B C) :
    Meets lim program 0 d [src, dst, A.size, B.size, C.size] μ (time A.size B.size C.size)
      (fun r ν =>
        r = (LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
          Seg ν dst (cells (records A B C)) ∧
            SameOutside μ ν dst (4 * LightBandEnumeration.count A.size B.size C.size)) := by sorry
