-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_sourceOnePlusY_map_eq_frobeniusProduct
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceOnePlusY_map_eq_frobeniusProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:28:10.226203+00:00
-- url     : https://prove2.me/theorems/10705121-f3d4-4fe2-a500-0a15588bde23
-- title:
--   Cartwright Steger: source One Plus Y map eq frobenius Product
-- statement:
--   The concrete power formula is exactly the LSV product of all Frobenius
--   conjugates of `1 + beta*X`; thus choosing `beta = 1` does not omit the norm
--   identity used by the source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L232-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/Arithmetic.lean#L232-L238

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceOnePlusY_map_eq_frobeniusProduct (P : BasePrime) (r : Rank) :
    (sourceOnePlusY P r).map
        (algebraMap (BaseField P) (ConstantExtension P r)) =
      ∏ i ∈ Finset.range r.matrixRank,
        (1 + Polynomial.C
          ((constantFrobenius P r ^ i) (beta P r)) * Polynomial.X) := by sorry
