-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_mul_constantRegularMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_mul_constantRegularMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:51:37.943802+00:00
-- url     : https://prove2.me/theorems/6b0b5475-aadc-4ab7-9a08-f08d88909667
-- title:
--   Cartwright Steger: frobenius GL mul constant Regular Matrix
-- statement:
--   Matrix form of the skew relation `Phi c = Frobenius(c) Phi`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L309-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L309-L322

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_mul_constantRegularMatrix
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) *
        constantRegularMatrix P r c =
      constantRegularMatrix P r (constantFrobenius P r c) *
        (frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) := by sorry
