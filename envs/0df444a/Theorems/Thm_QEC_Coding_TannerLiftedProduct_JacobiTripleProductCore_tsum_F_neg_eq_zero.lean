-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_neg_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:21.893198+00:00
-- url     : https://prove2.me/theorems/1984cf2d-b7e1-4d5c-ae96-a4842fae15b3
-- title:
--   Jacobi Triple Product Core: tsum F neg eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum F neg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1901-L1906
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1901-L1906

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_eq_zero : letI := piTop;
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) = 0 := by sorry
