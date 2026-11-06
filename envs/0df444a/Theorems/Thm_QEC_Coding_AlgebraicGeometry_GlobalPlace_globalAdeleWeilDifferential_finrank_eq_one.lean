-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferential_finrank_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferential_finrank_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:47.685485+00:00
-- url     : https://prove2.me/theorems/e61b6978-cb83-4140-8308-3c803d5c2049
-- title:
--   Global Place: global Adele Weil Differential finrank eq one
-- statement:
--   The space of intrinsic adelic Weil differentials is one-dimensional over
--   the function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L534-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L534-L694

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferential_finrank_eq_one :
    Module.finrank F (GlobalAdeleWeilDifferential k F) = 1 := by sorry
