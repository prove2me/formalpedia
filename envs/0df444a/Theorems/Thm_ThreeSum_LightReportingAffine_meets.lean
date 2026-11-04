-- Prove2me | Theorems.Thm_ThreeSum_LightReportingAffine_meets
-- name    : ThreeSum.LightReportingAffine.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:49.372488+00:00
-- url     : https://prove2.me/theorems/0f335353-3d19-4fa8-9603-c21ef095df25
-- title:
--   Light Reporting Affine: meets
-- statement:
--   The Light Reporting Affine construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingAffine.lean#L16-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingAffine.lean#L16-L31

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingAffine
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightReportingAffine.meets {p src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,b,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by sorry
