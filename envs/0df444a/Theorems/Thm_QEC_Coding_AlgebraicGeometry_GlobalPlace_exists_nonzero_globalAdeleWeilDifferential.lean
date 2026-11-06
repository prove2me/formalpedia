-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_nonzero_globalAdeleWeilDifferential
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_nonzero_globalAdeleWeilDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:30.373225+00:00
-- url     : https://prove2.me/theorems/e65df3a7-5835-4c6b-9b77-6fd002750c50
-- title:
--   Global Place: exists nonzero global Adele Weil Differential
-- statement:
--   A nonzero intrinsic adelic Weil differential exists.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L205-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L205-L211

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_nonzero_globalAdeleWeilDifferential :
    ∃ omega : GlobalAdeleWeilDifferential k F,
      GlobalAdeleWeilDifferential.IsNonzero omega := by sorry
