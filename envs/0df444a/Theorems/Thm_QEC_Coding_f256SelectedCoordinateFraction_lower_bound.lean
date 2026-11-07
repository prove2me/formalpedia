-- Prove2me | Theorems.Thm_QEC_Coding_f256SelectedCoordinateFraction_lower_bound
-- name    : QEC.Coding.f256SelectedCoordinateFraction_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:26.33844+00:00
-- url     : https://prove2.me/theorems/a26d3fb1-f133-4fcc-bb8a-7e72ec042212
-- title:
--   Coding: f256 Selected Coordinate Fraction lower bound
-- statement:
--   The explicit selected coordinate gives the normalized lower bound `1/512`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L98-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L98-L103

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256SelectedCoordinateFraction_lower_bound :
    (1 : ℚ) / 512 ≤ f256SelectedCoordinateFraction := by sorry
