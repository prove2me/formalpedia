-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueCyclicGeneratorMatrix_mul_residueConstantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueCyclicGeneratorMatrix_mul_residueConstantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:41:59.908384+00:00
-- url     : https://prove2.me/theorems/af05815d-ebfb-40ca-ba8a-29590bed46e4
-- title:
--   Cartwright Steger: residue Cyclic Generator Matrix mul residue Constant Matrix
-- statement:
--   The explicit residue generator obeys the same skew relation as the
--   cyclic-algebra symbol.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L236-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L236-L244

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueCyclicGeneratorMatrix_mul_residueConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    residueCyclicGeneratorMatrix P r level *
        residueConstantMatrix P r level c =
      residueConstantMatrix P r level (constantFrobenius P r c) *
        residueCyclicGeneratorMatrix P r level := by sorry
