-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_G_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_G_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:59.141404+00:00
-- url     : https://prove2.me/theorems/355c1ef5-8c7e-4037-b7c7-35fe9997e0b6
-- title:
--   Jacobi Triple Product Core: tsum G eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum G eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1813-L1816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1813-L1816

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_G_eq_zero (j : ℕ) : letI := piTop;
    ∑' ℓ : ℕ, ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by sorry
