-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_self_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.self_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:02.802864+00:00
-- url     : https://prove2.me/theorems/8d9bb886-61ab-4aac-894c-4e3f3c619bb2
-- title:
--   F256 Garcia Stichtenoth: self weak Different
-- statement:
--   The self extension contributes zero different exponent and index one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/RelativeTower.lean#L20-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/RelativeTower.lean#L20-L26

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.self_weakDifferent (R : Type*) [CommRing R] [IsDedekindDomain R]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    multiplicity H.asIdeal (differentIdeal R R) =
      2 * (H.asIdeal.ramificationIdx' H.asIdeal - 1) := by sorry
