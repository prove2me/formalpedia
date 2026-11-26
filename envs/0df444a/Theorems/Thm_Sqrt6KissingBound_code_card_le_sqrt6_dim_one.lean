-- Prove2me | Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_dim_one
-- name    : Sqrt6KissingBound.code_card_le_sqrt6_dim_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:14:33.228822+00:00
-- url     : https://prove2.me/theorems/6eed0206-c1ec-48ed-a247-a6f40b78a588
-- title:
--   Sqrt6 Kissing Bound: code card le sqrt6 dim one
-- statement:
--   The Sqrt6 Kissing Bound construction uses the code card le sqrt6 dim one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionOne.lean#L39-L47
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/DimensionOne.lean#L39-L47

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_DimensionOne
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.code_card_le_sqrt6_dim_one
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) :
    (X.card : ℝ) ≤ Real.sqrt 6 := by sorry
