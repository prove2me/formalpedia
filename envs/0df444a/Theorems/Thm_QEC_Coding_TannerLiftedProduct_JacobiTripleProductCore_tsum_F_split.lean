-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_split
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:21.00788+00:00
-- url     : https://prove2.me/theorems/cf082fc0-96e7-4759-acec-96b4a499bc4e
-- title:
--   Jacobi Triple Product Core: tsum F split
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum F split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1908-L1920
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1908-L1920

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_split : letI := piTop;
    (∑' (p : ℤ × ℕ), F p) =
    (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) +
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) := by sorry
