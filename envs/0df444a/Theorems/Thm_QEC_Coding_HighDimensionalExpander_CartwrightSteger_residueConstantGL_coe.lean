-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:48.415202+00:00
-- url     : https://prove2.me/theorems/2aba6e66-831f-44a6-aa97-0a22bc464ea9
-- title:
--   Cartwright Steger: residue Constant GL coe
-- statement:
--   The Cartwright Steger construction uses the residue Constant GL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L291-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L291-L298

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    (residueConstantGL P r level u :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      residueConstantMatrix P r level (u : ConstantExtension P r) := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
