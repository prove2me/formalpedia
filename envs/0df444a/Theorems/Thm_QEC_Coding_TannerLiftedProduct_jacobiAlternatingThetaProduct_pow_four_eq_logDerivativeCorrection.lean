-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
-- name    : QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:37:03.053207+00:00
-- url     : https://prove2.me/theorems/17a2070e-66c3-4657-ad83-8658c7f1bf12
-- title:
--   Tanner Lifted Product: jacobi Alternating Theta Product pow four eq log Derivative Correction
-- statement:
--   The cube-product identity, parity reindexing, and the two theta-product
--   specializations combine to identify the fourth power of the alternating
--   theta product with the logarithmic-derivative correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L22-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L22-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_eq_logDerivativeCorrection :
    jacobiAlternatingThetaProduct ^ 4 =
      1 + PowerSeries.C 4 * PowerSeries.X *
        jacobiLogDerivativeDifference := by sorry
