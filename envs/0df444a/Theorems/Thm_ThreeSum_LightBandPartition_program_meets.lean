-- Prove2me | Theorems.Thm_ThreeSum_LightBandPartition_program_meets
-- name    : ThreeSum.LightBandPartition.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:20:22.017739+00:00
-- url     : https://prove2.me/theorems/f6bf544f-a2e6-4807-88b8-47369418ba69
-- title:
--   Light Band Partition: program meets
-- statement:
--   The Light Band Partition construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L181-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L181-L191

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPartition.program_meets {src dst n g d : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    Meets lim program 0 d [src,n,g,dst] μ (time n g)
      (fun r μ' => r = (size n g : ℤ) ∧
        (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        (∀ i < size n g, μ' (dst+n+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (2*n)) := by sorry
