-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_add_principal_mem_globalAdeleVanishingDivisors_smul_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.add_principal_mem_globalAdeleVanishingDivisors_smul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:49:55.867903+00:00
-- url     : https://prove2.me/theorems/6d3660b2-d3a8-4dbc-a238-65ec5243b099
-- title:
--   Global Place: add principal mem global Adele Vanishing Divisors smul iff
-- statement:
--   Translating a divisor by the principal divisor of `x` is equivalent to
--   scaling the adelic Weil functional by `x`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialDuality.lean#L69-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialDuality.lean#L69-L100

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityAlgebra
attribute [local instance] globalAdeleDifferentialDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityScalarTower
attribute [local instance] globalAdeleDifferentialDualityScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialDualityRiemannRochFiniteDimensional
attribute [local instance] globalAdeleDifferentialDualityRiemannRochFiniteDimensional

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.add_principal_mem_globalAdeleVanishingDivisors_smul_iff
    (x : Fˣ) (omega : GlobalAdeleWeilDifferential k F)
    (D : Divisor (GlobalPlace k F)) :
    D + principalDivisor (k := k) (F := F) x ∈
        globalAdeleVanishingDivisors (k := k) (F := F)
          (GlobalAdeleWeilDifferential.smulWeil (x : F) omega) ↔
      D ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by sorry
