-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_differentIdeal_multiplicity_tower
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_multiplicity_tower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:37.897587+00:00
-- url     : https://prove2.me/theorems/9dd2c4a6-4b37-4bdc-a48a-c6ddbe3d05e7
-- title:
--   F256 Garcia Stichtenoth: different Ideal multiplicity tower
-- statement:
--   Multiplicity form of transitivity of the different ideal at a nonzero
--   prime chain `p ⊂ P ⊂ Q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/ExponentTower.lean#L41-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differents/ExponentTower.lean#L41-L89

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_ExponentTower
set_option autoImplicit false
open Module
attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.differentIdeal_multiplicity_tower
    (A B C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [IsDomain A] [IsDomain B]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [FaithfulSMul B C]
    (p : Ideal A) (P : Ideal B) (Q : Ideal C)
    [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    (hp : p ≠ ⊥) :
    multiplicity Q (differentIdeal A C) =
      multiplicity Q (differentIdeal B C) +
        P.ramificationIdx' Q * multiplicity P (differentIdeal A B) := by sorry
