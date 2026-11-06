-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_zero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:35.692964+00:00
-- url     : https://prove2.me/theorems/94d0603b-b92c-46fc-a2bb-d4ecdf39f2a5
-- title:
--   Global Place: riemann Roch Dimension zero
-- statement:
--   The zero-divisor Riemann--Roch dimension is one when `k` is the full
--   constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Constants.lean#L183-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Constants.lean#L183-L189

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Constants
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Polynomial
open scoped Polynomial RatFunc WithZero nonZeroDivisors
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_39
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_42
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_45
attribute [local instance] QEC.Coding.AlgebraicGeometry._p2m_local_instance_8dedd269c2_48
open QEC.Coding.AlgebraicGeometry.GlobalPlace

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_zero [IsFullConstantField k F]
    [FiniteDimensional k (riemannRochSubmodule
      (0 : Divisor (GlobalPlace k F)))] :
    riemannRochDimension (0 : Divisor (GlobalPlace k F)) = 1 := by sorry
