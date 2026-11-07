-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_baseScalarUnits
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_baseScalarUnits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:23.375474+00:00
-- url     : https://prove2.me/theorems/dc895770-db6c-4167-a775-2c7f3ed211be
-- title:
--   Cartwright Steger: nat Card base Scalar Units
-- statement:
--   The central scalar subgroup has exactly `q - 1` elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L537-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L537-L546

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_baseScalarUnits (P : BasePrime) (r : Rank) :
    Nat.card (baseScalarUnits P r) = P.q - 1 := by sorry
