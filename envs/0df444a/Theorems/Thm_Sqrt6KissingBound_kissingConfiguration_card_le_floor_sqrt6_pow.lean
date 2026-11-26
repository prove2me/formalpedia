-- Prove2me | Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_floor_sqrt6_pow
-- name    : Sqrt6KissingBound.kissingConfiguration_card_le_floor_sqrt6_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:12.965841+00:00
-- url     : https://prove2.me/theorems/58e786fa-198f-5041-adc4-5438ea832d14
-- title:
--   Sqrt6 Kissing Bound: kissing Configuration card le floor sqrt6 pow
-- statement:
--   The corresponding integer estimate.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingBound.lean#L40-L44
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingBound.lean#L40-L44

import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Definitions.Def_Sqrt6KissingBound_KissingBound
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.kissingConfiguration_card_le_floor_sqrt6_pow {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    X.card ≤ ⌊(Real.sqrt 6) ^ n⌋₊ := by sorry
