-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_heavyEvent_bound
-- name    : ThreeSum.TernaryCoverTrimming.heavyEvent_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:45:27.899735+00:00
-- url     : https://prove2.me/theorems/de7fb285-a2da-4c80-ba22-60a77fa77c19
-- title:
--   Ternary Cover Trimming: heavy Event bound
-- statement:
--   Markov's bound with denominator cleared.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L131-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L131-L152

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.heavyEvent_bound (x y : Word (ι := ι) (K := K)) (a b target : K)
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (B : ℕ)
    (hload : Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices vector target ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)))
    (hB : 8 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    8 * Fintype.card K ^ 2 * (heavyEvent (pairEvent x y a b) vertices vector target B).card ≤
      Fintype.card (Weight (ι := ι) (K := K)) := by sorry
