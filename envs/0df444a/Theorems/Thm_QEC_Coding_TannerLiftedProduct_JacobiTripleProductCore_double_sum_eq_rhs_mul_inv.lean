-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_eq_rhs_mul_inv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_eq_rhs_mul_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:29.167774+00:00
-- url     : https://prove2.me/theorems/6deb5c47-07b2-4525-841c-273d6f318402
-- title:
--   Jacobi Triple Product Core: double sum eq rhs mul inv
-- statement:
--   The Jacobi Triple Product Core construction uses the double sum eq rhs mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1979-L1990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1979-L1990

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_eq_rhs_mul_inv : letI := piTop;
    (∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    rhs * PowerSeries.invOfUnit (qPochhammerInf (-q * aI) (q ^ 2)) 1 := by sorry
