-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawA_Procs_meets_candidates
-- name    : ThreeSum.LightBandRawA.Procs.meets_candidates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:14.125772+00:00
-- url     : https://prove2.me/theorems/3a161edc-3ff2-4243-8a8b-f4bdfb0c48e5
-- title:
--   Procs: meets candidates
-- statement:
--   The physical candidate list supplies every successful A-index validity
--   fact required by the actual incidence loop.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L188-L205
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean#L188-L205

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_LightBandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}

theorem ThreeSum.LightBandRawA.Procs.meets_candidates {pMain : ℕ} (S : Procs P pMain) (A B C : BandEnumeration.Family)
    (hA : A.size = BandPartition.size n g) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 2 < lim.depth) (hg : 0 < g)
    (hrecords : records + 4 * (BandCandidateRows.records A B C).length ≤ vals) (hsrc : src + n ≤ vals)
    (hspace : space vals (BandCandidateRows.records A B C).length g ≤ lim.space)
    (hword : (word n g (BandCandidateRows.records A B C).length : ℤ) ≤ lim.word)
    (hrecordRead : Seg μ records (cells (BandCandidateRows.records A B C))) (hread : ∀ j < n, μ (src + j) = f j) :
    Meets lim P pMain d [records, (BandCandidateRows.records A B C).length, src, n, g, vals] μ
      (time (BandCandidateRows.records A B C).length g)
      (fun r ν =>
        r = ((items n g (BandCandidateRows.records A B C)).length : ℤ) ∧
          Stored ν vals (ownerBase vals (BandCandidateRows.records A B C).length g)
              (positionBase vals (BandCandidateRows.records A B C).length g) f
              (items n g (BandCandidateRows.records A B C)) ∧
            Kept μ ν vals) := by sorry
