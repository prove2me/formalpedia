-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerGeneratorGL_apply_first_second
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerGeneratorGL_apply_first_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:01.623502+00:00
-- url     : https://prove2.me/theorems/726b56ba-ec42-47af-84b3-9af291d94f67
-- title:
--   Cartwright Steger: index Cartwright Steger Generator GL apply first second
-- statement:
--   The first superdiagonal entry records the Frobenius ratio of the
--   constant-class representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L277-L296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L277-L296

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerGeneratorGL_apply_first_second
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    (indexCartwrightStegerGeneratorGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) =
      -indexConstantEmbedding P r level
        ((u : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (u : ConstantExtension P r))⁻¹) := by sorry
