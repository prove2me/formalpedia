-- Prove2me | Theorems.Thm_ThreeSum_LightOneHot_program_meets
-- name    : ThreeSum.LightOneHot.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:42.392733+00:00
-- url     : https://prove2.me/theorems/11fd3335-5b73-4a77-9e80-2259e30bcd3a
-- title:
--   Light One Hot: program meets
-- statement:
--   The Light One Hot construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L176-L189
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L176-L189

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOneHot.program_meets {μ : ℕ → ℤ} {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hm : m < 2^L) (hd : d+L+1 ≤ lim.depth)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim program 0 d [L,m,src0,src1,work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧
        Powers μ' work L ∧ SameOutside μ μ' work (L+1)) := by sorry
