-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_injective
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:27.538451+00:00
-- url     : https://prove2.me/theorems/e081bd94-9d8c-4ed9-a713-1e036335b8e6
-- title:
--   Global Place: global Adele Smul Into Differential Space injective
-- statement:
--   The Global Place construction uses the global Adele Smul Into Differential Space injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L495-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L495-L523

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_injective
    (omega : GlobalAdeleWeilDifferential k F)
    {D₀ : Divisor (GlobalPlace k F)}
    (hD₀ : D₀ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (E : Divisor (GlobalPlace k F)) (homega : omega.toFun ≠ 0) :
    Function.Injective
      (globalAdeleSmulIntoDifferentialSpace
        (k := k) (F := F) omega hD₀ E) := by sorry
