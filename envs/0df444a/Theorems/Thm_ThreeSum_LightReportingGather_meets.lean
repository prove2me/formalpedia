-- Prove2me | Theorems.Thm_ThreeSum_LightReportingGather_meets
-- name    : ThreeSum.LightReportingGather.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:39.84786+00:00
-- url     : https://prove2.me/theorems/81268f0b-3dd9-4121-a576-d9c7891c7a37
-- title:
--   Light Reporting Gather: meets
-- statement:
--   The Light Reporting Gather construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGather.lean#L21-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGather.lean#L21-L49

import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGather
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingGather.meets {μ : ℕ → ℤ} {p indices src dst t n d : ℕ}
    (hp : P[p]? = some body) (index : ℕ → ℕ) (value : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrc : src+n ≤ lim.space) (hdst : dst+t ≤ lim.space)
    (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src+i) = value i)
    (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim P p d [indices,src,dst,t,n] μ (time t)
      (fun _ ν => (∀ i < t, ν (dst+i) = value (index i)) ∧ SameOutside μ ν dst t) := by sorry
