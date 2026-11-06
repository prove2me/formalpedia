-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDerivation_rationalEquiv
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_rationalEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:46:26.030112+00:00
-- url     : https://prove2.me/theorems/f47a6eb1-7ed0-4943-93a3-031966dcce82
-- title:
--   Function Field Differential: function Field Derivation rational Equiv
-- statement:
--   The chain rule, without changing the target's chosen rational-base algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L21-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean#L21-L43

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDerivation_rationalEquiv (e : RatFunc k ≃ₐ[k] K) (f : RatFunc k) :
    functionFieldDerivation (k := k) (e f) =
      e (functionFieldDerivation (k := k) f) *
        functionFieldDerivation (k := k) (e RatFunc.X) := by sorry
