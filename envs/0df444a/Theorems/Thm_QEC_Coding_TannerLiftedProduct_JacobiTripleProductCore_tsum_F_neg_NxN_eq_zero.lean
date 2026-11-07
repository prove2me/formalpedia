-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_neg_NxN_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_NxN_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:24.453788+00:00
-- url     : https://prove2.me/theorems/16c7a2e2-6958-4d89-bd09-8d634d41dfbd
-- title:
--   Jacobi Triple Product Core: tsum F neg Nx N eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum F neg Nx N eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1891-L1899
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1891-L1899

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_neg_NxN_eq_zero : letI := piTop;
    (∑' (c : ℕ × ℕ), F (-(↑c.1 + 1), c.2)) = 0 := by sorry
