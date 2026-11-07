-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_sameParity_weight
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_sameParity_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:43.414201+00:00
-- url     : https://prove2.me/theorems/6f46e1dd-b078-4490-9d5b-cf6b680eacd2
-- title:
--   Tanner Lifted Product: jacobi same Parity weight
-- statement:
--   Weight conversion on the equal-parity chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L117-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L117-L120

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobi_sameParity_weight (s t : ℤ) :
    (2 * (s + t) + 1) * (2 * (s - t) + 1) =
      (2 * s + 1) ^ 2 - (2 * t) ^ 2 := by sorry
