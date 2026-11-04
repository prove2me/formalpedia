-- Prove2me | Theorems.Thm_ThreeSum_LightOneHot_setup_meets
-- name    : ThreeSum.LightOneHot.setup_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:17:46.719849+00:00
-- url     : https://prove2.me/theorems/9473684d-32ab-4b70-b030-40a80b4fb919
-- title:
--   Light One Hot: setup meets
-- statement:
--   The Light One Hot construction uses the setup meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L133-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOneHot.lean#L133-L172

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOneHot.setup_meets {pMain pPowers pHash : ℕ}
    (hmain : P[pMain]? = some (setupBody pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody)
    (hhash : P[pHash]? = some (body pHash))
    {μ : ℕ → ℤ} {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hm : m < 2^L) (hd : d+L+1 ≤ lim.depth)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,m,src0,src1,work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧
        Powers μ' work L ∧ SameOutside μ μ' work (L+1)) := by sorry
