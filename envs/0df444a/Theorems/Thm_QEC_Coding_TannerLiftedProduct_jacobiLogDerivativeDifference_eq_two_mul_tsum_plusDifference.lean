-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference
-- name    : QEC.Coding.TannerLiftedProduct.jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:37:35.897745+00:00
-- url     : https://prove2.me/theorems/1c78f95a-373b-4cb1-aa2b-96b7fbcc683a
-- title:
--   Tanner Lifted Product: jacobi Log Derivative Difference eq two mul tsum plus Difference
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Log Derivative Difference eq two mul tsum plus Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L327-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L327-L342

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference :
    jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        (jacobiPlusLogDerivative (2 * (n + 1)) -
          jacobiPlusLogDerivative (2 * n + 1)) := by sorry
