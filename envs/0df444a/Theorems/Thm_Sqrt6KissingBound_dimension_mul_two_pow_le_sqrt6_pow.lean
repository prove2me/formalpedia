-- Prove2me | Theorems.Thm_Sqrt6KissingBound_dimension_mul_two_pow_le_sqrt6_pow
-- name    : Sqrt6KissingBound.dimension_mul_two_pow_le_sqrt6_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:14:20.162814+00:00
-- url     : https://prove2.me/theorems/3d7b502c-e403-448a-b643-e79048e99901
-- title:
--   Sqrt6 Kissing Bound: dimension mul two pow le sqrt6 pow
-- statement:
--   The Sqrt6 Kissing Bound construction uses the dimension mul two pow le sqrt6 pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeBounds.lean#L91-L133
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeBounds.lean#L91-L133

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.dimension_mul_two_pow_le_sqrt6_pow :
    ∀ n : ℕ, 6 ≤ n → (n : ℝ) * (2 : ℝ) ^ (n - 1) ≤ (Real.sqrt 6) ^ n := by sorry
