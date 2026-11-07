-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_single_mul_general
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:12.485803+00:00
-- url     : https://prove2.me/theorems/0238af49-87e4-4f4f-bbe2-e50487f9919f
-- title:
--   Jacobi Triple Product Core: coeff single mul general
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff single mul general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1622-L1624
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1622-L1624

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul_general (e : ℤ) (c : LaurentPolynomial ℤ) (f : S_hahn) (b : ℤ) :
    (HahnSeries.single e c * f).coeff b = c * f.coeff (b - e) := by sorry
