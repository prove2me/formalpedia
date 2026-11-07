-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tsum_CS_mul_t_pow
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_CS_mul_t_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:23.59193+00:00
-- url     : https://prove2.me/theorems/ee721296-090c-4db7-ac3b-9ce5e3b8426e
-- title:
--   Jacobi Triple Product Core: coeff tsum CS mul t pow
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff tsum CS mul t pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L633-L638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L633-L638

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_CS_mul_t_pow (c : ℕ → R) (n : ℕ) :
    @PowerSeries.coeff R _ n (letI := piTopS; ∑' k, CS (c k) * t ^ k) = c n := by sorry
