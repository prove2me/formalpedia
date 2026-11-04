-- Prove2me | Theorems.Thm_ThreeSum_LightReportingGatherPair_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingGatherPair.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:11:37.624088+00:00
-- url     : https://prove2.me/theorems/658c397d-ce4f-4787-b45f-08bfbaa6c122
-- title:
--   Light Reporting Gather Pair: program meets
-- statement:
--   The Light Reporting Gather Pair construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGatherPair.lean#L18-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGatherPair.lean#L18-L49

import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGatherPair
open Light
variable {lim : Limits}

theorem ThreeSum.LightReportingGatherPair.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {indices srcL srcR dstL dstR t n d : ℕ}
    (index : ℕ → ℕ) (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrcL : srcL+n ≤ lim.space) (hsrcR : srcR+n ≤ lim.space)
    (hdstL : dstL+t ≤ lim.space) (hdstR : dstR+t ≤ lim.space)
    (hsepIL : Apart indices t dstL t) (hsepIR : Apart indices t dstR t)
    (hsepLL : Apart srcL n dstL t) (hsepRL : Apart srcR n dstL t)
    (hsepRR : Apart srcR n dstR t) (hsepOut : Apart dstL t dstR t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadL : ∀ i < n, μ (srcL+i) = left i) (hreadR : ∀ i < n, μ (srcR+i) = right i)
    (hwordL : ∀ i < n, |left i| ≤ lim.word) (hwordR : ∀ i < n, |right i| ≤ lim.word)
    (hd : d < lim.depth) :
    Meets lim program 1 d [indices,srcL,srcR,t,n,dstL,dstR] μ (time t)
      (fun _ ν => Seg ν dstL (List.ofFn fun i : Fin t => left (index i.val)) ∧
        Seg ν dstR (List.ofFn fun i : Fin t => right (index i.val)) ∧
        SameOutside2 μ ν dstL t dstR t) := by sorry
