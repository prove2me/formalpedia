-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
-- name    : ThreeSum.LightReportingFilter.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:37:33.544995+00:00
-- url     : https://prove2.me/theorems/5a2dd086-4cb5-4999-bdab-ef8af8a54668
-- title:
--   Light Reporting Filter: program meets
-- statement:
--   The Light Reporting Filter construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L114-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFilter.lean#L114-L123

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightReportingFilter.program_meets {n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    Meets lim program 0 d [n,src,dst] μ (time n)
      (fun r μ' => r = ((selected count n).length : ℤ) ∧
        SegN μ' dst (selected count n) ∧ SameOutside μ μ' dst n) := by sorry
