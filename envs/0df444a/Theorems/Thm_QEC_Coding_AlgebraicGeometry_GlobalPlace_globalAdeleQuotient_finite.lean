-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleQuotient_finite
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotient_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:13:40.620203+00:00
-- url     : https://prove2.me/theorems/95ec5660-2904-4455-b88c-11202caef675
-- title:
--   Global Place: global Adele Quotient finite
-- statement:
--   The intrinsic adele quotient is finite-dimensional over the full constant
--   field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L122-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleQuotient.lean#L122-L171

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleQuotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleQuotientScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotientFilterModule

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleQuotient_finite
    (D : Divisor (GlobalPlace k F)) :
    Module.Finite k (GlobalAdeleQuotient (k := k) (F := F) D) := by sorry
