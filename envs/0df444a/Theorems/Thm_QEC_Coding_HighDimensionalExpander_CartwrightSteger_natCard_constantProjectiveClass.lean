-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_constantProjectiveClass
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:25.455239+00:00
-- url     : https://prove2.me/theorems/3d2a0fc2-0793-43bc-b571-3e2de65c9c19
-- title:
--   Cartwright Steger: nat Card constant Projective Class
-- statement:
--   The projective constant classes have the geometric-series cardinality
--   of the projective points over the base field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L568-L576
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L568-L576

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_constantProjectiveClass
    (P : BasePrime) (r : Rank) :
    Nat.card (ConstantProjectiveClass P r) =
      ∑ i ∈ Finset.range r.matrixRank, P.q ^ i := by sorry
