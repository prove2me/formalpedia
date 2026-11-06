-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_le_add_degree_of_le
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_le_add_degree_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:54:32.991767+00:00
-- url     : https://prove2.me/theorems/17ac0ba5-5389-43b0-acbd-04137bbe6fdd
-- title:
--   Global Place: riemann Roch Dimension le add degree of le
-- statement:
--   For comparable divisors, the dimension growth is bounded by the weighted
--   degree of their effective difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveIncrement.lean#L183-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveIncrement.lean#L183-L198

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementAlgebra
attribute [local instance] riemannRochEffectiveIncrementAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementScalarTower
attribute [local instance] riemannRochEffectiveIncrementScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensionalRiemannRochSubmodule
attribute [local instance] finiteDimensionalRiemannRochSubmodule

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_le_add_degree_of_le
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochDimension E ≤
      riemannRochDimension D +
        (Divisor.degree (residueDegree (k := k) (F := F)) (E - D)).toNat := by sorry
