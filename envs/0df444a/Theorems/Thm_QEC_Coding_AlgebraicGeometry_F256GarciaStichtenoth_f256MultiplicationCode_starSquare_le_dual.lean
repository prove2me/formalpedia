-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCode_starSquare_le_dual
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_starSquare_le_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:25:43.93237+00:00
-- url     : https://prove2.me/theorems/209cf35a-ecad-4e0b-a06f-e201af77fe64
-- title:
--   F256 Garcia Stichtenoth: f256 Multiplication Code star Square le dual
-- statement:
--   The actual unit-residue differential gives the paper's multiplication property.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L28-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/NormalClosureEvaluation.lean#L28-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationCode_starSquare_le_dual (i : ℕ) :
    agStarProduct (f256MultiplicationCode i) (f256MultiplicationCode i) ≤
      (f256MultiplicationCode i).dual.carrier := by sorry
