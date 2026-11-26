-- Prove2me | Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_high
-- name    : Sqrt6KissingBound.code_card_le_sqrt6_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:13:42.039798+00:00
-- url     : https://prove2.me/theorems/8f93a2d3-4344-46e6-bf45-9d47cfbaad1c
-- title:
--   Sqrt6 Kissing Bound: code card le sqrt6 high
-- statement:
--   The Sqrt6 Kissing Bound construction uses the code card le sqrt6 high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeBounds.lean#L135-L159
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/BiconeBounds.lean#L135-L159

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.code_card_le_sqrt6_high {k : ℕ} (hk : 4 ≤ k)
    (X : Finset (EuclideanSpace ℝ (Fin (k + 2))))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ (k + 2) := by sorry
