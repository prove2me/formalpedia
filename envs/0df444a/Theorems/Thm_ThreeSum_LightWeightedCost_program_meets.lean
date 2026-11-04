-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
-- name    : ThreeSum.LightWeightedCost.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:13.095219+00:00
-- url     : https://prove2.me/theorems/127c9553-635b-4c4e-a712-cb91d062bbff
-- title:
--   Light Weighted Cost: program meets
-- statement:
--   The Light Weighted Cost construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L135-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L135-L144

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_LightCost
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedCost.program_meets {N m powers d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((1025*N+1100 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,m,powers] μ (time N)
      (fun r ν => r=(partialCost N m N : ℤ) ∧ ν=μ) := by sorry
