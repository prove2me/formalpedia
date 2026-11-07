-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerGeneratorGL_apply_self
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerGeneratorGL_apply_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:49.180966+00:00
-- url     : https://prove2.me/theorems/ebb3bd55-3cc3-41f1-863e-01129587a642
-- title:
--   Cartwright Steger: index Cartwright Steger Generator GL apply self
-- statement:
--   Conjugation by a represented constant preserves the unit diagonal of
--   `b = 1 - z⁻¹`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L254-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L254-L267

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerGeneratorGL_apply_self
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) (i : Fin r.matrixRank) :
    (indexCartwrightStegerGeneratorGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) i i = 1 := by sorry
