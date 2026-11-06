-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleVanishingDivisor_le_differentialDivisor
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisor_le_differentialDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:48:03.073566+00:00
-- url     : https://prove2.me/theorems/77174614-aa81-4daf-bebc-3e3045d1653b
-- title:
--   Global Place: global Adele Vanishing Divisor le differential Divisor
-- statement:
--   Every vanishing divisor of the realized functional is bounded above by
--   the intrinsic divisor of the original nonzero differential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L338-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialWeil.lean#L338-L387

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisor_le_differentialDivisor
    (omega : Differential k F) (homega : omega ≠ 0)
    {D : Divisor (GlobalPlace k F)}
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega)) :
    D ≤ FunctionFieldDifferential.differentialDivisor
      (k := k) (F := F) omega homega := by sorry
