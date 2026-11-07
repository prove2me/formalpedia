-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_eq_g_comp_reindex
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_eq_g_comp_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:47.404145+00:00
-- url     : https://prove2.me/theorems/ce1f2562-a8c1-4f6f-b824-624b2d7ec299
-- title:
--   Jacobi Triple Product Core: lhs eq g comp reindex
-- statement:
--   The Jacobi Triple Product Core construction uses the lhs eq g comp reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1402-L1408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1402-L1408

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_eq_g_comp_reindex (p : ℤ × ℕ) :
    letI := piTop;
    (PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    g (reindexEquiv p) := by sorry
