-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueFrobeniusMatrix_mul_residueConstantMatrix
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFrobeniusMatrix_mul_residueConstantMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:37:35.300199+00:00
-- url     : https://prove2.me/theorems/b363e640-0317-46c2-9f36-95f27e457489
-- title:
--   Cartwright Steger: residue Frobenius Matrix mul residue Constant Matrix
-- statement:
--   Reduction preserves the constant-field skew relation.  Notice that the
--   Frobenius acts only on `F_(q^d)`: no action on, or embedding into,
--   `F_(q^e)` is postulated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L57-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/ResidueRepresentation.lean#L57-L66

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueFrobeniusMatrix_mul_residueConstantMatrix
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    residueFrobeniusMatrix P r level * residueConstantMatrix P r level c =
      residueConstantMatrix P r level (constantFrobenius P r c) *
        residueFrobeniusMatrix P r level := by sorry
