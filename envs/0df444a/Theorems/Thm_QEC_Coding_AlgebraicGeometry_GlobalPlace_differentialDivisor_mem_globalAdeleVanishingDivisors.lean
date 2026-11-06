-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_differentialDivisor_mem_globalAdeleVanishingDivisors
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_mem_globalAdeleVanishingDivisors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:49.427039+00:00
-- url     : https://prove2.me/theorems/9d55f9ef-2b9b-4ff7-b217-6cb645316ace
-- title:
--   Global Place: differential Divisor mem global Adele Vanishing Divisors
-- statement:
--   The intrinsic divisor of a nonzero differential is a vanishing divisor
--   of its realized adelic Weil functional.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L248-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L248-L256

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_mem_globalAdeleVanishingDivisors
    (omega : Differential k F) (homega : omega ≠ 0) :
    FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega ∈
      globalAdeleVanishingDivisors (k := k) (F := F)
        (globalAdeleWeilDifferentialOfDifferential
          (k := k) (F := F) omega homega) := by sorry
