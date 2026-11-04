-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFilter_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingFilter.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:37.23658+00:00
-- url     : https://prove2.me/theorems/affffdfc-c7aa-4709-b160-d6a73e000794
-- title:
--   Light Reporting Filter: meets
-- statement:
--   The Light Reporting Filter construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L59-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L59-L110

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Theorems.Thm_ThreeSum_LightReportingAffine_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingFilter.meets_w3sum_ac885d1 {p n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    Meets lim P p d [n,src,dst] μ (time n)
      (fun r μ' => r = ((selected count n).length : ℤ) ∧
        SegN μ' dst (selected count n) ∧ SameOutside μ μ' dst n) := by sorry
