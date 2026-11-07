-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_eq_tsum_G
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_eq_tsum_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:28.965083+00:00
-- url     : https://prove2.me/theorems/247d5142-9a70-4609-91c6-5f562f1804ef
-- title:
--   Jacobi Triple Product Core: tsum F eq tsum G
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum F eq tsum G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1922-L1926
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1922-L1926

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_F_eq_tsum_G : letI := piTop;
    (∑' p : ℤ × ℕ, F p) = (∑' p : ℕ × ℕ, G p) := by sorry
