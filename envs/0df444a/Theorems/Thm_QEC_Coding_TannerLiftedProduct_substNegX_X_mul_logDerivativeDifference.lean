-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_substNegX_X_mul_logDerivativeDifference
-- name    : QEC.Coding.TannerLiftedProduct.substNegX_X_mul_logDerivativeDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:37:12.667369+00:00
-- url     : https://prove2.me/theorems/dea014c7-0f74-48e1-8fab-6899fdcbe95a
-- title:
--   Tanner Lifted Product: subst Neg X X mul log Derivative Difference
-- statement:
--   The Tanner Lifted Product construction uses the subst Neg X X mul log Derivative Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L370-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L370-L387

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.substNegX_X_mul_logDerivativeDifference :
    substNegX (PowerSeries.X * jacobiLogDerivativeDifference) =
      2 * ∑' n : ℕ,
        (jacobiLambertTerm (2 * (n + 1)) -
          jacobiLambertTerm (4 * (n + 1)) +
          jacobiLambertTerm (2 * n + 1)) := by sorry
