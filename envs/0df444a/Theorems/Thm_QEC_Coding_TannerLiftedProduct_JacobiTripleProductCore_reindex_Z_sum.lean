-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_reindex_Z_sum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reindex_Z_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:48.621201+00:00
-- url     : https://prove2.me/theorems/ad9c41a4-f82c-4085-83c1-351f0dc53ec7
-- title:
--   Jacobi Triple Product Core: reindex Z sum
-- statement:
--   The Jacobi Triple Product Core construction uses the reindex Z sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1410-L1422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1410-L1422

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reindex_Z_sum : letI := piTop;
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by sorry
