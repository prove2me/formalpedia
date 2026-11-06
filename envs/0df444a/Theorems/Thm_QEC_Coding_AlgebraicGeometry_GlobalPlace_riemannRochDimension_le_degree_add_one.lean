-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_le_degree_add_one
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_le_degree_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:56:06.19551+00:00
-- url     : https://prove2.me/theorems/efc15946-27c3-459e-abf2-f2e91a33fed3
-- title:
--   Global Place: riemann Roch Dimension le degree add one
-- statement:
--   Over the full constant field, the dimension of an effective
--   Riemann--Roch divisor is at most its weighted degree plus one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveDimensionBound.lean#L51-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveDimensionBound.lean#L51-L62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Constants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveDimensionBoundAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveDimensionBoundScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochEffectiveDimensionBoundFiniteDimensional

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_le_degree_add_one [IsFullConstantField k F]
    (E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    riemannRochDimension E ≤
      (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat + 1 := by sorry
