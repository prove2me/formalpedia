-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_oppositeParity_weight
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:49.973815+00:00
-- url     : https://prove2.me/theorems/98a4d419-8aec-4a5c-9121-5dd8ded0d8d9
-- title:
--   Tanner Lifted Product: jacobi opposite Parity weight
-- statement:
--   After the odd parity sign is included, the opposite-parity chart has
--   the same transformed weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L124-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L124-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_weight (s t : ℤ) :
    -(2 * (s + t) + 1) * (2 * (t - s - 1) + 1) =
      (2 * s + 1) ^ 2 - (2 * t) ^ 2 := by sorry
