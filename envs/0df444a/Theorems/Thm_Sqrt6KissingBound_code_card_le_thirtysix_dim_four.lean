-- Prove2me | Theorems.Thm_Sqrt6KissingBound_code_card_le_thirtysix_dim_four
-- name    : Sqrt6KissingBound.code_card_le_thirtysix_dim_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:16:59.464122+00:00
-- url     : https://prove2.me/theorems/7fda2062-894c-43f8-bb8e-1bf3e02eb59c
-- title:
--   Sqrt6 Kissing Bound: code card le thirtysix dim four
-- statement:
--   The Sqrt6 Kissing Bound construction uses the code card le thirtysix dim four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L183-L217
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionFour.lean#L183-L217

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

theorem Sqrt6KissingBound.code_card_le_thirtysix_dim_four
    (X : Finset (EuclideanSpace ℝ (Fin 4)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 36 := by sorry
