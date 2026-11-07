-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_div_one_add
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_div_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:26.064944+00:00
-- url     : https://prove2.me/theorems/405cad6e-511d-4897-9902-b58960d74037
-- title:
--   Cartwright Steger: index Place Y div one add
-- statement:
--   The selected unit is exactly `y / (1 + y)`, so its proved full
--   power-class order is the LSV finite-image index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L380-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean#L380-L400

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_div_one_add
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPlaceY P r level / (1 + indexPlaceY P r level) =
      (indexRatioUnit P r level : ResidueField P r level) := by sorry
