-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass_mul_baseScalar
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass_mul_baseScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:48:54.475284+00:00
-- url     : https://prove2.me/theorems/529677e3-0e01-4975-b98a-8b2feb825b98
-- title:
--   Cartwright Steger: nat Card constant Projective Class mul base Scalar
-- statement:
--   Exact size equation for the source generator index
--   `F_(q^d)^× / F_q^×`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L550-L564
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L550-L564

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass_mul_baseScalar
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) * (P.q - 1) =
      P.q ^ r.matrixRank - 1 := by sorry
