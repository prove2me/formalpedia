-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:59:50.837419+00:00
-- url     : https://prove2.me/theorems/ca7fd815-7ad5-4c8a-9b14-7ca54aff7db1
-- title:
--   Cartwright Steger: skew Laurent To Global Matrix single
-- statement:
--   The Cartwright Steger construction uses the skew Laurent To Global Matrix single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRepresentation.lean#L256-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewRepresentation.lean#L256-L263

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ)
    (c : ConstantExtension P r) :
    skewLaurentToGlobalMatrix P r (SkewMonoidAlgebra.single n c) =
      constantMatrix P r c * globalCyclicZMatrixHom P r n := by sorry
