-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_top
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_different_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:54:40.923166+00:00
-- url     : https://prove2.me/theorems/9c6bb1b3-01da-4cea-93b5-7c0bb948238c
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal different eq top
-- statement:
--   An integral parameter gives the unit different on the actual quadratic
--   field, not merely on its isomorphic polynomial model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L61-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L61-L88

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_different_eq_top
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (a : K) (ha : 0 ≤ P.order a)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤) :
    differentIdeal P.valuationRing (integralClosure P.valuationRing L) = ⊤ := by sorry
