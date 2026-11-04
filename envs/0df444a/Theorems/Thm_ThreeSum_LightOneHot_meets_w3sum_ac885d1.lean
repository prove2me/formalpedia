-- Prove2me | Theorems.Thm_ThreeSum_LightOneHot_meets_w3sum_ac885d1
-- name    : ThreeSum.LightOneHot.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:45.346764+00:00
-- url     : https://prove2.me/theorems/8424d137-5678-485b-8e60-b0b30628717b
-- title:
--   Light One Hot: meets
-- statement:
--   The Light One Hot construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L38-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L38-L125

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOneHot.meets_w3sum_ac885d1 {pHash W powers src0 src1 U : ℕ}
    (hprog : P[pHash]? = some (body pHash))
    (μ : ℕ → ℤ) (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hsrc0 : src0+W ≤ lim.space) (hsrc1 : src1+W ≤ lim.space)
    (hword : (word W U : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hread0 : ∀ i < W, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < W, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < W, w0 i ≤ U) (hbound1 : ∀ i < W, w1 i ≤ U) :
    ∀ L m : ℕ, L ≤ W → m < 2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pHash d [L,m,W,powers,src0,src1] μ (time L)
        (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧ μ' = μ) := by sorry
