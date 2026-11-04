-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
-- name    : ThreeSum.LightLocalCoverSchedule.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:51:31.843197+00:00
-- url     : https://prove2.me/theorems/a7586e5f-298c-4ee7-bab6-c61c8fec5874
-- title:
--   Light Local Cover Schedule: program meets
-- statement:
--   The Light Local Cover Schedule construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L141-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean#L141-L163

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding

theorem ThreeSum.LightLocalCoverSchedule.program_meets {lim : Light.Limits} {d : ℕ}
    {μ : ℕ → ℤ} {h src activePtr : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hsrc : src+rows h*cols h ≤ activePtr)
    (hspace : activePtr+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h) ≤ lim.space)
    (hread : ∀ i < rows h, ∀ r < cols h, μ (src+i*cols h+r) = (matrix h i r : ℤ))
    (hword : (1 : ℤ) ≤ lim.word) :
    Light.Meets lim LightCoverGreedy.program 0 d [src,activePtr,rows h,cols h,scheduleSize h] μ
      (LightCoverGreedy.time (rows h) (cols h) (scheduleSize h))
      (fun r μ' => r = (LightCoverGreedy.out activePtr (rows h) (cols h) : ℤ) ∧
        (∀ s : Occurrence h,
          μ' (LightCoverGreedy.out activePtr (rows h) (cols h)+s.val) = (candidateAt h s : ℤ)) ∧
        Light.SameOutside μ μ' activePtr (LightCoverGreedy.total (rows h) (cols h) (scheduleSize h))) := by sorry
