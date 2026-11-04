-- Prove2me | Theorems.Thm_ThreeSum_LightHistogram_histogram_meets_w3sum_ac885d1
-- name    : ThreeSum.LightHistogram.histogram_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:03.816071+00:00
-- url     : https://prove2.me/theorems/6b334be5-d6e6-4a34-81f8-03074ed53a02
-- title:
--   Light Histogram: histogram meets
-- statement:
--   Actual clearing, incrementing, and memory-preservation contract.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHistogram.lean#L104-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHistogram.lean#L104-L127

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightHistogram.histogram_meets_w3sum_ac885d1 {pHist pFill : ℕ}
    (hp : P[pHist]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdepth : d < lim.depth)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p) :
    Meets lim P pHist d [(src : ℤ), dst, n, p] μ (histogramTime n p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = count key r n) ∧ SameOutside μ μ' dst p := by sorry
