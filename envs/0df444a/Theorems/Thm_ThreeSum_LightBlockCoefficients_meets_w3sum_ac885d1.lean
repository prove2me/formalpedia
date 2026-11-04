-- Prove2me | Theorems.Thm_ThreeSum_LightBlockCoefficients_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBlockCoefficients.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:23.273574+00:00
-- url     : https://prove2.me/theorems/6167835a-2497-45c3-a6ad-41e8ef0d32dc
-- title:
--   Light Block Coefficients: meets
-- statement:
--   The Light Block Coefficients construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L66-L208
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockCoefficients.lean#L66-L208

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Theorems.Thm_ThreeSum_LightScaleArray_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBlockCoefficients.meets_w3sum_ac885d1 {pMain pPowers pScale : ℕ}
    (hmain : P[pMain]? = some (body pPowers pScale))
    (hpowers : P[pPowers]? = some powTableBody)
    (hscale : P[pScale]? = some LightScaleArray.body)
    {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim P pMain d [J,L,p,occ,maps,dst0,dst1,work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧
        Kept μ ν dst0 ∧ Powers ν work J p) := by sorry
