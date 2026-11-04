-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceHashes_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBlockSourceHashes.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:41.235194+00:00
-- url     : https://prove2.me/theorems/b97a2357-909b-42ca-9599-40dbb7a0e6b8
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L50-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L50-L141

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceHashes.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ}
    (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hd : d+J*L+2 ≤ lim.depth) (hspace : space work J L ≤ lim.space)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work) (hword : (word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^(J*L)) :
    Meets lim P pMain d [J,L,p,occ,maps,coeff0,coeff1,masks,rawLeft,rawRight,n,work]
      μ (time J L n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ Kept μ ν coeff0) := by sorry
