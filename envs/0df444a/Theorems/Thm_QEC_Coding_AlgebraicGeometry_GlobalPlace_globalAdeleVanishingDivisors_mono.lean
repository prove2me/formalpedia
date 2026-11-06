-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleVanishingDivisors_mono
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisors_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:32:31.903464+00:00
-- url     : https://prove2.me/theorems/2bd745a8-b6f8-4a3a-b711-f3333dcaab1e
-- title:
--   Global Place: global Adele Vanishing Divisors mono
-- statement:
--   The Global Place construction uses the global Adele Vanishing Divisors mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L398-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleWeilDifferential.lean#L398-L406

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisors_mono
    {omega : GlobalAdeleWeilDifferential k F}
    {D E : Divisor (GlobalPlace k F)} (hED : E ≤ D)
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega) :
    E ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by sorry
