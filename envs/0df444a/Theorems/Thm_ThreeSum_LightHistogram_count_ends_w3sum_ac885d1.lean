-- Prove2me | Theorems.Thm_ThreeSum_LightHistogram_count_ends_w3sum_ac885d1
-- name    : ThreeSum.LightHistogram.count_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:10.396305+00:00
-- url     : https://prove2.me/theorems/0fbd3e49-d0bf-4227-b70b-8a2104e1c439
-- title:
--   Light Histogram: count ends
-- statement:
--   The Light Histogram construction uses the count ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHistogram.lean#L45-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHistogram.lean#L45-L96

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightHistogram
set_option autoImplicit false
open ThreeSum ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightHistogram.count_ends_w3sum_ac885d1 {μ : ℕ → ℤ} {loc : ℕ → ℤ} {src dst n p : ℕ}
    (key : ℕ → ℕ) (hsrc : loc 0 = src) (hdst : loc 1 = dst) (hlen : loc 2 = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst + r) = 0) :
    Ends lim P d countBody ⟨loc, μ⟩ (countTime n) fun σ' =>
      (∀ r < p, σ'.mem (dst + r) = count key r n) ∧
        SameOutside μ σ'.mem dst p := by sorry
