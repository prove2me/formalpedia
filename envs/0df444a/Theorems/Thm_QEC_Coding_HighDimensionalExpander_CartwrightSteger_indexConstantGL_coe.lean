-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:40:25.297882+00:00
-- url     : https://prove2.me/theorems/282a0fd6-87f5-4ee7-8362-742bdf080ee3
-- title:
--   Cartwright Steger: index Constant GL coe
-- statement:
--   The Cartwright Steger construction uses the index Constant GL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L238-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSplitting.lean#L238-L245

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    (indexConstantGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      indexConstantMatrix P r level u := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
