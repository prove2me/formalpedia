-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_rationalEquiv
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_rationalEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:43.576195+00:00
-- url     : https://prove2.me/theorems/3987657f-21ce-4e50-9818-8b6ec56efb19
-- title:
--   Function Field Differential: differential Generator order rational Equiv
-- statement:
--   Intrinsic differential order under a rational field equivalence. The
--   order identity is the defining equality of the transported place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L49-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L49-L77

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable [Finite k]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_rationalEquiv
    (e : RatFunc k ≃ₐ[k] K) (P : GlobalPlace k K)
    (R : GlobalPlace k (RatFunc k)) (horder : ∀ f, P.order (e f) = R.order f) :
    ∃ _hd : functionFieldDerivation (k := k) (e RatFunc.X) ≠ 0,
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero =
      differentialOrder R (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        functionFieldDifferentialGenerator_ne_zero -
      P.order (functionFieldDerivation (k := k) (e RatFunc.X)) := by sorry
