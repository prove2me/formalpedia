-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_left_loadedMass_bound
-- name    : ThreeSum.TernaryCoverTrimming.left_loadedMass_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:45:26.530812+00:00
-- url     : https://prove2.me/theorems/6e2b78fd-6530-4406-8bd7-4ca7fd6d05f4
-- title:
--   Ternary Cover Trimming: left loaded Mass bound
-- statement:
--   The Ternary Cover Trimming construction uses the left loaded Mass bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L42-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L42-L75

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.left_loadedMass_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (vertices : Finset (Word (ι := ι) (K := K))) :
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices leftVector a ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by sorry
