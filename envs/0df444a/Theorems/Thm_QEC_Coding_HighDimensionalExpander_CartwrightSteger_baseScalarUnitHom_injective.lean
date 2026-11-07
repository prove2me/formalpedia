-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_baseScalarUnitHom_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseScalarUnitHom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:52:16.396942+00:00
-- url     : https://prove2.me/theorems/f03b6b6e-6635-4e40-b858-3f6d43c5aed0
-- title:
--   Cartwright Steger: base Scalar Unit Hom injective
-- statement:
--   The Cartwright Steger construction uses the base Scalar Unit Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L517-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L517-L520

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.baseScalarUnitHom_injective (P : BasePrime) (r : Rank) :
    Function.Injective (baseScalarUnitHom P r) := by sorry
