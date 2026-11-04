-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawACatalog_program_meets
-- name    : ThreeSum.LightBandRawACatalog.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:39:00.579549+00:00
-- url     : https://prove2.me/theorems/871c4add-5b22-4110-be96-f83ff1aba55b
-- title:
--   Light Band Raw ACatalog: program meets
-- statement:
--   The Light Band Raw ACatalog construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L142-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawACatalog.lean#L142-L163

import Definitions.Def_Submission_ThreeSum_LightBandCandidates
import Definitions.Def_Submission_ThreeSum_LightBandRawA
import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Theorems.Thm_ThreeSum_LightBandCandidates_program_meets
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBandPartition_program_meets
import Theorems.Thm_ThreeSum_LightBandRawA_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightHeaderBands_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightNormalize_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSortedBands_program_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawACatalog
open Light BandEnumeration BandCandidateRows BandRawA
set_option maxHeartbeats 2100000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {tables rec src headerA headerB headerC nA nB nC g vals : ℕ}
  {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawACatalog.program_meets (A B C : Family) (hA : A.size = BandPartition.size nA g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 3 < lim.depth) (hg : 0 < g)
    (htable : tables + LightBandEnumeration.count A.size B.size C.size ≤ rec) (hsrc : src + nA ≤ rec)
    (hheadA : headerA + 2 ≤ rec) (hheadB : headerB + 2 ≤ rec) (hheadC : headerC + 2 ≤ rec)
    (hrec : rec + 4 * LightBandEnumeration.count A.size B.size C.size ≤ vals)
    (hspace : space vals A.size B.size C.size g ≤ lim.space) (hword : (word nA A.size B.size C.size g : ℤ) ≤ lim.word)
    (hheaderA : LightHeaderBands.At μ headerA nA A) (hheaderB : LightHeaderBands.At μ headerB nB B)
    (hheaderC : LightHeaderBands.At μ headerC nC C) (htables : LightBandEnumeration.Tables μ tables A B C)
    (hread : ∀ j < nA, μ (src + j) = f j) :
    Meets lim program 0 d [tables, rec, src, headerA, headerB, headerC, g, vals] μ (time A.size B.size C.size g)
      (fun r ν =>
        r = ((items nA g (records A B C)).length : ℤ) ∧
          Seg ν rec (cells (records A B C)) ∧
            Stored ν vals (LightBandRawA.ownerBase vals (LightBandEnumeration.count A.size B.size C.size) g)
                (LightBandRawA.positionBase vals (LightBandEnumeration.count A.size B.size C.size) g) f
                (items nA g (records A B C)) ∧
              Kept μ ν rec) := by sorry
