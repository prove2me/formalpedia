-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:33:36.901021+00:00
-- url     : https://prove2.me/theorems/44d3eb9f-a857-4138-8a13-da4860d7f394
-- title:
--   Cartwright Steger: residue BGL coe
-- statement:
--   The Cartwright Steger construction uses the residue BGL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L272-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L272-L278

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueBGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      residueBMatrix P r level := by sorry
