-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_trimmedPairEvent_bound
-- name    : ThreeSum.TernaryCoverTrimming.trimmedPairEvent_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:09.691535+00:00
-- url     : https://prove2.me/theorems/e766ae40-c559-43ea-81cb-8be5e5082b13
-- title:
--   Ternary Cover Trimming: trimmed Pair Event bound
-- statement:
--   The Ternary Cover Trimming construction uses the trimmed Pair Event bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L159-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L159-L185

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_WeightedCache3SUM_Alias_9cba9841773c016e

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.trimmedPairEvent_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (VL VR : Finset (Word (ι := ι) (K := K))) (B : ℕ)
    (hBL : 8 * (Fintype.card K + VL.card) ≤ B * Fintype.card K)
    (hBR : 8 * (Fintype.card K + VR.card) ≤ B * Fintype.card K) :
    3 * Fintype.card (Weight (ι := ι) (K := K)) ≤
      4 * Fintype.card K ^ 2 * (trimmedPairEvent x y a b VL VR B).card := by sorry
