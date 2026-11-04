-- Prove2me | Theorems.Thm_ThreeSum_LightMinimum_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMinimum.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:09.763343+00:00
-- url     : https://prove2.me/theorems/83e203bd-134c-430e-bfde-fef233990fea
-- title:
--   Light Minimum: meets
-- statement:
--   The Light Minimum construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L65-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMinimum.lean#L65-L99

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
set_option autoImplicit false
open ThreeSum ThreeSum.LightMinimum
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightMinimum.meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {src n : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n)
    (hsrc : src+n ≤ lim.space)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src, n] μ (time n)
      fun r μ' => r = (least f n : ℤ) ∧ μ' = μ := by sorry
