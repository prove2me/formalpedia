-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_ramificationIdx_eq_one_of_unit_different
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.ramificationIdx_eq_one_of_unit_different
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:55:35.626799+00:00
-- url     : https://prove2.me/theorems/f3cbb5ee-9eb1-4ffa-aa69-f4db7a5c9dda
-- title:
--   F256 Garcia Stichtenoth: ramification Idx eq one of unit different
-- statement:
--   A unit different gives ramification index one at every actual upper
--   prime of a finite separable integral model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L132-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L132-L144

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
omit [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.ramificationIdx_eq_one_of_unit_different
    {O : Type*} [CommRing O] [Algebra O K] [IsFractionRing O K]
    [Algebra O L] [IsScalarTower O K L]
    [IsDedekindDomain O] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    [Module.IsTorsionFree O (integralClosure O L)]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    [H.asIdeal.LiesOver p]
    (hd : differentIdeal O (integralClosure O L) = ⊤) :
    p.ramificationIdx' H.asIdeal = 1 := by sorry
