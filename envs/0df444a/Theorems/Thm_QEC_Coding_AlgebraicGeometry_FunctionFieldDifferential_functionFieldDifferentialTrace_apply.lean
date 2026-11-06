-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialTrace_apply
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialTrace_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:54.150196+00:00
-- url     : https://prove2.me/theorems/8db20134-2ea3-4476-9861-bcd9a290e1ab
-- title:
--   Function Field Differential: function Field Differential Trace apply
-- statement:
--   Evaluation of the differential trace in the global `dX` coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialTrace.lean#L42-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialTrace.lean#L42-L47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.functionFieldDifferentialTrace_apply (omega : Differential k F) :
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      Algebra.trace (RatFunc k) F
          (functionFieldDifferentialCoordinate (k := k) (F := F) omega) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by sorry
