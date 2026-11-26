-- Prove2me | Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_cube
-- name    : Sqrt6KissingBound.code_card_le_sqrt6_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:15:39.890138+00:00
-- url     : https://prove2.me/theorems/af01087f-ef88-539e-b8a5-e3ec6328da0a
-- title:
--   Sqrt6 Kissing Bound: code card le sqrt6 cube
-- statement:
--   The Sqrt6 Kissing Bound construction uses the code card le sqrt6 cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L155-L168
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionThree.lean#L155-L168

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

theorem Sqrt6KissingBound.code_card_le_sqrt6_cube
    (X : Finset (EuclideanSpace ℝ (Fin 3)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 3 := by sorry
