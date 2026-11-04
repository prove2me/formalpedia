-- Prove2me | Theorems.Thm_ThreeSum_LightTernarySourceHistogram_scale_meets
-- name    : ThreeSum.LightTernarySourceHistogram.scale_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:55:17.613692+00:00
-- url     : https://prove2.me/theorems/85b5ffb6-af97-4b20-b49c-3dc28ebc3912
-- title:
--   Light Ternary Source Histogram: scale meets
-- statement:
--   The Light Ternary Source Histogram construction uses the scale meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L25-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernarySourceHistogram.lean#L25-L45

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernarySourceHistogram.scale_meets {p base n U : ℕ} (hp : P[p]? = some scaleBody)
    (μ : ℕ → ℤ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+n ≤ lim.space)
    (hvalues : ∀ j < n, |μ (base+j)| ≤ U)
    (hweight : (weight : ℤ) ≤ lim.word)
    (hword : (weight : ℤ)*(U : ℤ) ≤ lim.word) :
    Meets lim P p d [base,n,weight] μ (scaleTime n) (fun _ μ' =>
      (∀ j < n, μ' (base+j) = (weight : ℤ)*μ (base+j)) ∧
        SameOutside μ μ' base n) := by sorry
