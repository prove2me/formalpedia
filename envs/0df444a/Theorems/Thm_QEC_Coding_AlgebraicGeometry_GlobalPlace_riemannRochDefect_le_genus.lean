-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDefect_le_genus
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDefect_le_genus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:09:45.110561+00:00
-- url     : https://prove2.me/theorems/a3fbb9dd-8995-409d-bb7e-ef5cc25251b6
-- title:
--   Global Place: riemann Roch Defect le genus
-- statement:
--   Every actual defect is bounded by the genus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Genus.lean#L342-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Genus.lean#L342-L350

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDefect_le_genus
    (D : Divisor (GlobalPlace k F)) :
    riemannRochDefect (k := k) (F := F) D ≤
      (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) := by sorry
