-- Prove2me | Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
-- name    : ThreeSum.LightLocalParameters.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:09:58.39562+00:00
-- url     : https://prove2.me/theorems/43d87a0d-ed7b-478c-87e2-c53874dbf996
-- title:
--   Light Local Parameters: program meets
-- statement:
--   The Light Local Parameters construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalParameters.lean#L140-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalParameters.lean#L140-L146

import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Definitions.Def_Submission_ThreeSum_LightSelectedPrime
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalParameters
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalParameters.program_meets {μ : ℕ → ℤ} {h dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+5 ≤ lim.depth)
    (hout : dst+8 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r μ' => r = (localPrime h : ℤ) ∧ Seg μ' dst (values h) ∧
        KeptBut μ μ' work dst 8) := by sorry
