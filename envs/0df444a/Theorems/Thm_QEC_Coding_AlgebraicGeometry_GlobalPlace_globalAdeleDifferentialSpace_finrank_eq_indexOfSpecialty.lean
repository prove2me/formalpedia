-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:09.415203+00:00
-- url     : https://prove2.me/theorems/aa5ed5a8-1a2e-413d-a0cb-4ea18b8287ad
-- title:
--   Global Place: global Adele Differential Space finrank eq index Of Specialty
-- statement:
--   The rank of the fixed-divisor adelic differential space is the intrinsic
--   index of specialty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L140-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L140-L153

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
    (D : Divisor (GlobalPlace k F)) :
    Module.finrank k (globalAdeleDifferentialSpace (k := k) (F := F) D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by sorry
