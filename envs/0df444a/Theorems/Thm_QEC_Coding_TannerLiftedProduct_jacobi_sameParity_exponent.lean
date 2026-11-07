-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_sameParity_exponent
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_sameParity_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:28.866537+00:00
-- url     : https://prove2.me/theorems/64ee38da-a7d3-40b5-9a7b-ee6aa4a9f1ae
-- title:
--   Tanner Lifted Product: jacobi same Parity exponent
-- statement:
--   Quadratic exponent conversion on the equal-parity chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L105-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L105-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobi_sameParity_exponent (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (s - t) ^ 2 + (s - t) =
      2 * (s ^ 2 + s + t ^ 2) := by sorry
