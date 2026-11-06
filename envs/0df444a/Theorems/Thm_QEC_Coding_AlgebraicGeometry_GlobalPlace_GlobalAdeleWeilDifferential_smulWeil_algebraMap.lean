-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_GlobalAdeleWeilDifferential_smulWeil_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential.smulWeil_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:33:15.271911+00:00
-- url     : https://prove2.me/theorems/44d6babd-56eb-4366-96d4-b7e39b4928b2
-- title:
--   Global Adele Weil Differential: smul Weil algebra Map
-- statement:
--   The Global Adele Weil Differential construction uses the smul Weil algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L366-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L366-L370

import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilAlgebra
attribute [local instance] globalAdeleWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleWeilScalarTower
attribute [local instance] globalAdeleWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilRiemannRochFiniteDimensional
attribute [local instance] globalAdeleWeilRiemannRochFiniteDimensional
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpaceFinite
attribute [local instance] globalAdeleDifferentialSpaceFinite
open QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential
variable {k F}

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.GlobalAdeleWeilDifferential.smulWeil_algebraMap (c : k)
    (omega : GlobalAdeleWeilDifferential k F)
    (a : GlobalAdele (k := k) (F := F)) :
    (smulWeil (algebraMap k F c) omega).toFun a = c • omega.toFun a := by sorry
