-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_loadedMass_eq
-- name    : ThreeSum.TernaryCoverTrimming.loadedMass_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:45:14.131528+00:00
-- url     : https://prove2.me/theorems/f5e15290-a01d-4c70-bfde-fb056db93503
-- title:
--   Ternary Cover Trimming: loaded Mass eq
-- statement:
--   The Ternary Cover Trimming construction uses the loaded Mass eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L32-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L32-L40

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.loadedMass_eq (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) :
    loadedMass event vertices vector a =
      ∑ u ∈ vertices, (event.filter fun w => linearHash (vector u) w = a).card := by sorry
