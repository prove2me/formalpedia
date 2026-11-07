-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_a_pow_eq_C_T
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.a_pow_eq_C_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:54.902406+00:00
-- url     : https://prove2.me/theorems/e9daace7-e8ba-413f-8819-560270211ae6
-- title:
--   Jacobi Triple Product Core: a pow eq C T
-- statement:
--   The Jacobi Triple Product Core construction uses the a pow eq C T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1071-L1076
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1071-L1076

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.a_pow_eq_C_T (k : ℕ) :
    (a : R) ^ k = PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by sorry
