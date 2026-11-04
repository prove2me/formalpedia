-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_linear_update_full
-- name    : ThreeSum.LightKaratsuba.linear_update_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:49.192509+00:00
-- url     : https://prove2.me/theorems/bb2955e5-900a-449a-9160-95b318080f29
-- title:
--   Light Karatsuba: linear update full
-- statement:
--   The Light Karatsuba construction uses the linear update full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L113-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L113-L130

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.LightKaratsuba.linear_update_full {μ μ' : ℕ → ℤ} {out src offset n N : ℕ}
    {c : ℤ} {f g : ℕ → ℤ} (hfit : offset + n ≤ N)
    (hOld : ∀ j < N, μ (out + j) = f j)
    (hSrc : ∀ i < n, μ (src + i) = g i)
    (hWrite : ∀ i < n,
      μ' (out + offset + i) = μ (out + offset + i) + c * μ (src + i))
    (hkeep : SameOutside μ μ' (out + offset) n) :
    ∀ j < N, μ' (out + j) = f j + window (fun i => c * g i) offset n j := by sorry
