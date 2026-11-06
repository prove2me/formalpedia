-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_weakDifferent_tower_of_fractionFields
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.weakDifferent_tower_of_fractionFields
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:08.302171+00:00
-- url     : https://prove2.me/theorems/70fe828b-9d9f-4bd1-b298-d3ca76aaf2e3
-- title:
--   F256 Garcia Stichtenoth: weak Different tower of fraction Fields
-- statement:
--   The weak different law composes using the actual specified fraction
--   fields; canonical-fraction separability is proved internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/RelativeTower.lean#L30-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/RelativeTower.lean#L30-L60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.weakDifferent_tower_of_fractionFields
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
    [Algebra A K] [IsFractionRing A K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra.IsSeparable K L]
    (p : IsDedekindDomain.HeightOneSpectrum A)
    (P : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C)
    [P.asIdeal.LiesOver p.asIdeal] [Q.asIdeal.LiesOver P.asIdeal]
    (hAB : multiplicity P.asIdeal (differentIdeal A B) =
      2 * (p.asIdeal.ramificationIdx' P.asIdeal - 1))
    (hBC : multiplicity Q.asIdeal (differentIdeal B C) =
      2 * (P.asIdeal.ramificationIdx' Q.asIdeal - 1)) :
    multiplicity Q.asIdeal (differentIdeal A C) =
      2 * (p.asIdeal.ramificationIdx' Q.asIdeal - 1) := by sorry
