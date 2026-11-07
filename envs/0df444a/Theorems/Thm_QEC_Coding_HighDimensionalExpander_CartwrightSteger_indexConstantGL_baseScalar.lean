-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_baseScalar
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_baseScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:23.761918+00:00
-- url     : https://prove2.me/theorems/5bf88592-6d86-45b1-bf69-ab0768797169
-- title:
--   Cartwright Steger: index Constant GL base Scalar
-- statement:
--   Base-field constants act by scalar matrices in the compatible split
--   model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L220-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L220-L230

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_baseScalar
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (BaseField P)ˣ) :
    indexConstantGL P r level (baseScalarUnitHom P r a) =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        (indexBaseScalarUnit P r level a) := by sorry
