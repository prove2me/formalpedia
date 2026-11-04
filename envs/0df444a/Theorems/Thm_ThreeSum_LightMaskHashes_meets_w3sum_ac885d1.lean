-- Prove2me | Theorems.Thm_ThreeSum_LightMaskHashes_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskHashes.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:41.842017+00:00
-- url     : https://prove2.me/theorems/a10eaddd-ec63-450d-a77f-6f671709c500
-- title:
--   Light Mask Hashes: meets
-- statement:
--   The Light Mask Hashes construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskHashes.lean#L38-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskHashes.lean#L38-L119

import Definitions.Def_Submission_ThreeSum_LightOneHot
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskHashes
open Light LightSubsetAddress
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightMaskHashes.meets_w3sum_ac885d1 {pMain pPowers pHash : ℕ}
    (hmain : P[pMain]? = some (body pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody)
    (hhash : P[pHash]? = some (LightOneHot.body pHash))
    {μ : ℕ → ℤ} {L masks dst n src0 src1 work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hsrc0 : src0+L ≤ dst) (hsrc1 : src1+L ≤ dst)
    (hdst : dst+n ≤ work)
    (hword : (LightOneHot.word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,masks,dst,n,src0,src1,work] μ (time L n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = (OneHotMask.eval w0 w1 L (mask i) : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst n) := by sorry
