-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
-- name    : QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:09:39.899552+00:00
-- url     : https://prove2.me/theorems/c3a156e6-612d-4786-a661-a9dec36290b0
-- title:
--   Tanner Lifted Product: jacobi Parity Reindex inl
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Parity Reindex inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L96-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean#L96-L98

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl (s t : ℤ) :
    jacobiParityReindex (Sum.inl (s, t)) = (s + t, s - t) := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
