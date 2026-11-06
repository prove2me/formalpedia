-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochIndexOfSpecialty_eq
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochIndexOfSpecialty_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:09:53.761536+00:00
-- url     : https://prove2.me/theorems/3266b3cb-a41e-4427-80e9-7dd030bb6540
-- title:
--   Global Place: riemann Roch Index Of Specialty eq
-- statement:
--   The integer value of the index of specialty is the Riemann--Roch
--   correction left after the genus lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Genus.lean#L373-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Genus.lean#L373-L384

import Mathlib.Data.Int.LeastGreatest
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochGenusAlgebra
attribute [local instance] riemannRochGenusAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochGenusScalarTower
attribute [local instance] riemannRochGenusScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochGenusFiniteDimensional
attribute [local instance] riemannRochGenusFiniteDimensional
variable [IsFullConstantField k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochIndexOfSpecialty_eq
    (D : Divisor (GlobalPlace k F)) :
    (riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D : ℤ) =
      (riemannRochDimension D : ℤ) -
        (Divisor.degree (residueDegree (k := k) (F := F)) D + 1 -
          (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
            (φ := φ) (s := s) k F : ℤ)) := by sorry
