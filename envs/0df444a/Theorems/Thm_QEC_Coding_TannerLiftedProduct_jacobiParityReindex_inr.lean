-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
-- name    : QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:45.146381+00:00
-- url     : https://prove2.me/theorems/6f32fe3f-79db-498c-ad08-e327c6eb2274
-- title:
--   Tanner Lifted Product: jacobi Parity Reindex inr
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Parity Reindex inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L100-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L100-L102

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr (s t : ℤ) :
    jacobiParityReindex (Sum.inr (s, t)) = (s + t, t - s - 1) := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
