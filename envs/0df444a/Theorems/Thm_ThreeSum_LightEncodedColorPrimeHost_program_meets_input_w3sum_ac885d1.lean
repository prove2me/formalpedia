-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorPrimeHost_program_meets_input_w3sum_ac885d1
-- name    : ThreeSum.LightEncodedColorPrimeHost.program_meets_input_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:02:16.604111+00:00
-- url     : https://prove2.me/theorems/3a5db987-55b1-463f-8a4d-a7e1ed7743f1
-- title:
--   Light Encoded Color Prime Host: program meets input
-- statement:
--   The Light Encoded Color Prime Host construction uses the program meets input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeHost.lean#L61-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightEncodedColorPrimeHost.lean#L61-L158

import Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrimeHost
open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
set_option maxHeartbeats 3200000
set_option maxRecDepth 15000
variable {lim : Limits} {d : ℕ}

theorem ThreeSum.LightEncodedColorPrimeHost.program_meets_input_w3sum_ac885d1 {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : inputSpace free n U ≤ lim.space) (hword : (inputWord n U : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 71 d [src,n,params,row,free] μ (inputTime n U)
      (fun r ν => r=(prime free n (bandSize n) : ℤ) ∧
        EncodedColorPrimeReadyData.Output ν free n color x ∧ Kept μ ν free) := by sorry
