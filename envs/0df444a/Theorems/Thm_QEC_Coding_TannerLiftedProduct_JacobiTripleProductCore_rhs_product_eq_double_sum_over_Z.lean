-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_product_eq_double_sum_over_Z
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_product_eq_double_sum_over_Z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:49.90065+00:00
-- url     : https://prove2.me/theorems/cec9d02c-6368-4a40-9e6f-9d718474e17c
-- title:
--   Jacobi Triple Product Core: rhs product eq double sum over Z
-- statement:
--   The Jacobi Triple Product Core construction uses the rhs product eq double sum over Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1376-L1389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1376-L1389

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_product_eq_double_sum_over_Z : letI := piTop;
    rhs * (∑' ℓ : ℕ, (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by sorry
