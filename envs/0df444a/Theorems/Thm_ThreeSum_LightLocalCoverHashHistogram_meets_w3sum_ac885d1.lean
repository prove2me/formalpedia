-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverHashHistogram_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverHashHistogram.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:01.561819+00:00
-- url     : https://prove2.me/theorems/163a5c12-1c83-46cc-be2f-b449dd271cae
-- title:
--   Light Local Cover Hash Histogram: meets
-- statement:
--   The Light Local Cover Hash Histogram construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverHashHistogram.lean#L21-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverHashHistogram.lean#L21-L96

import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightLocalCoverHashHistogram
import Theorems.Thm_ThreeSum_LightHashHistogram_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverHashHistogram
open Light LightHashHistogram
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCoverHashHistogram.meets_w3sum_ac885d1 {pMain : ℕ} (S : LightHashHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {L masks raw codes hist n src0 src1 p work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hp : 0 < p) (hspace : space work L U ≤ lim.space)
    (hmasks : masks+n ≤ raw) (hsrc0 : src0+L ≤ raw) (hsrc1 : src1+L ≤ raw)
    (hraw : raw+n ≤ codes) (hcodes : codes+n ≤ hist) (hhist : hist+p ≤ work)
    (hword : (word L p U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,masks,raw,codes,hist,n,src0,src1,p,work] μ (time L n p U)
      (fun _ μ' =>
        (∀ i < n, μ' (codes+i) = (code L p mask w0 w1 i : ℤ)) ∧
        (∀ r < p, μ' (hist+r) = (LightHistogram.count (code L p mask w0 w1) r n : ℤ)) ∧
        Kept μ μ' raw ∧ Preserved μ μ' work raw codes hist n p) := by sorry
