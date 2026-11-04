-- Prove2me | Theorems.Thm_ThreeSum_LightReportingGather_program_meets
-- name    : ThreeSum.LightReportingGather.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:27.131432+00:00
-- url     : https://prove2.me/theorems/94660744-c2ae-4e40-8179-a98b9a910325
-- title:
--   Light Reporting Gather: program meets
-- statement:
--   The Light Reporting Gather construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGather.lean#L51-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingGather.lean#L51-L68

import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGather
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingGather.program_meets {μ : ℕ → ℤ} {indices src dst t n d : ℕ}
    (index : ℕ → ℕ) (value : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrc : src+n ≤ lim.space) (hdst : dst+t ≤ lim.space)
    (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src+i) = value i)
    (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim program 0 d [indices,src,dst,t,n] μ (time t)
      (fun _ ν => Seg ν dst (List.ofFn fun i : Fin t => value (index i.val)) ∧
        SameOutside μ ν dst t) := by sorry
