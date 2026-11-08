-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_X_mul_jacobiLogDerivativeDifference_eq_tsum
-- name    : QEC.Coding.TannerLiftedProduct.X_mul_jacobiLogDerivativeDifference_eq_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:36:53.17133+00:00
-- url     : https://prove2.me/theorems/594388ca-278b-4c8d-8045-6942bc844413
-- title:
--   Tanner Lifted Product: X mul jacobi Log Derivative Difference eq tsum
-- statement:
--   The Tanner Lifted Product construction uses the X mul jacobi Log Derivative Difference eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L351-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L351-L368

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.X_mul_jacobiLogDerivativeDifference_eq_tsum :
    PowerSeries.X * jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        PowerSeries.X *
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1)) := by sorry
