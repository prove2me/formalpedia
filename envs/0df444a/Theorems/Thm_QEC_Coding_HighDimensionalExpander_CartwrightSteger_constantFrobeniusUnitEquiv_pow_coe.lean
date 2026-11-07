-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobeniusUnitEquiv_pow_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobeniusUnitEquiv_pow_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:58:20.153781+00:00
-- url     : https://prove2.me/theorems/e914df14-5bb1-489b-ac94-1a6f18e335c5
-- title:
--   Cartwright Steger: constant Frobenius Unit Equiv pow coe
-- statement:
--   Coercing a Frobenius power on units agrees with the corresponding
--   power of the constant-field automorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L441-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L441-L451

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobeniusUnitEquiv_pow_coe
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    (((constantFrobeniusUnitEquiv P r ^ j) u :
        (ConstantExtension P r)ˣ) : ConstantExtension P r) =
      (constantFrobenius P r ^ j) (u : ConstantExtension P r) := by sorry
