-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverTrimming_right_loadedMass_bound
-- name    : ThreeSum.TernaryCoverTrimming.right_loadedMass_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:45:23.269664+00:00
-- url     : https://prove2.me/theorems/1f9674e4-ce6a-4ad3-a106-4c0ad24880c9
-- title:
--   Ternary Cover Trimming: right loaded Mass bound
-- statement:
--   The Ternary Cover Trimming construction uses the right loaded Mass bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L77-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean#L77-L110

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.TernaryCoverTrimming.right_loadedMass_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (vertices : Finset (Word (ι := ι) (K := K))) :
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices rightVector b ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by sorry
