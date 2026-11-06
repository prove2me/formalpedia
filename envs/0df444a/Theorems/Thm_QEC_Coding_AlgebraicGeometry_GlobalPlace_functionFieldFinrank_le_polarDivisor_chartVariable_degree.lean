-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_functionFieldFinrank_le_polarDivisor_chartVariable_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldFinrank_le_polarDivisor_chartVariable_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:58:34.970042+00:00
-- url     : https://prove2.me/theorems/7aa2874f-8967-43f0-8fbd-383449de3a0a
-- title:
--   Global Place: function Field Finrank le polar Divisor chart Variable degree
-- statement:
--   The dimension-growth family forces the chart variable's pole-divisor
--   degree to dominate the rational-function extension degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarFamily.lean#L415-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarFamily.lean#L415-L493

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyAlgebra
attribute [local instance] riemannRochPolarFamilyAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarFamilyRationalScalarTower
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPolarFamilyFiniteDimensional
attribute [local instance] riemannRochPolarFamilyFiniteDimensional

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.functionFieldFinrank_le_polarDivisor_chartVariable_degree
    [IsFullConstantField k F] :
    Module.finrank (RatFunc k) F ≤
      (Divisor.degree (residueDegree (k := k) (F := F))
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F)))).toNat := by sorry
