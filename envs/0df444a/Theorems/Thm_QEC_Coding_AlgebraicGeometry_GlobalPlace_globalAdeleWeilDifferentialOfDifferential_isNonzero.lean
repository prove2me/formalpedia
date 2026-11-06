-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferentialOfDifferential_isNonzero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_isNonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:24.341208+00:00
-- url     : https://prove2.me/theorems/668533d6-2494-42bf-aab2-71aea49ab415
-- title:
--   Global Place: global Adele Weil Differential Of Differential is Nonzero
-- statement:
--   The residue extension of a nonzero differential is itself a nonzero
--   adelic Weil functional.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L217-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L217-L244

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilScalarTower
attribute [local instance] globalAdeleDifferentialWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleWeilDifferentialOfDifferential_isNonzero
    (omega : Differential k F) (homega : omega ≠ 0) :
    GlobalAdeleWeilDifferential.IsNonzero
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega) := by sorry
