-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_oppositeParity_exponent
-- name    : QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:35.702889+00:00
-- url     : https://prove2.me/theorems/f8af498f-0315-4a3a-a4f3-67b8b708431d
-- title:
--   Tanner Lifted Product: jacobi opposite Parity exponent
-- statement:
--   Quadratic exponent conversion on the opposite-parity chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L111-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L111-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_exponent (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (t - s - 1) ^ 2 + (t - s - 1) =
      2 * (s ^ 2 + s + t ^ 2) := by sorry
