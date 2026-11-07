-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_zero_of_constantFrobenius_pow_eq_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_zero_of_constantFrobenius_pow_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:57:54.444058+00:00
-- url     : https://prove2.me/theorems/3b260bc4-d52e-41d5-8006-d2a8658608e9
-- title:
--   Cartwright Steger: eq zero of constant Frobenius pow eq one
-- statement:
--   A Frobenius power in the canonical exponent range can be the identity
--   only at exponent zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L305-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L305-L312

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_zero_of_constantFrobenius_pow_eq_one
    (P : BasePrime) (r : Rank) (j : ℕ) (hj : j < r.matrixRank)
    (hpow : constantFrobenius P r ^ j = 1) :
    j = 0 := by sorry
