-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_C_T_mul_q_pow_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_C_T_mul_q_pow_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:12.52849+00:00
-- url     : https://prove2.me/theorems/4a17b5b4-6b41-4b4e-b6c7-ac42b187278b
-- title:
--   Jacobi Triple Product Core: coeff C T mul q pow eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff C T mul q pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1264-L1269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1264-L1269

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_C_T_mul_q_pow_eq_zero (d : ℕ) (m : ℤ) (hm : d < m.natAbs ^ 2) :
    (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) = 0 := by sorry
