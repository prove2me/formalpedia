-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_eq_of_order_eq
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_eq_of_order_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:05:05.608756+00:00
-- url     : https://prove2.me/theorems/8dd83168-6147-4e2a-bbb9-935783e8b3b1
-- title:
--   Function Field Differential: differential Generator order eq of order eq
-- statement:
--   The Function Field Differential construction uses the differential Generator order eq of order eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialPlaceTransport.lean#L46-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialPlaceTransport.lean#L46-L62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
attribute [local instance] QEC.Coding.AlgebraicGeometry.placeTransportDVR
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_eq_of_order_eq (P Q : GlobalPlace k K)
    (horder : P.order = Q.order) :
    differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero =
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero := by sorry
