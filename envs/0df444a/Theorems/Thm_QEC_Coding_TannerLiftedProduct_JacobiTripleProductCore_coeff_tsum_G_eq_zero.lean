-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tsum_G_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_G_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:52.711118+00:00
-- url     : https://prove2.me/theorems/14fd6dc6-d558-4ef6-a634-1c6722e18788
-- title:
--   Jacobi Triple Product Core: coeff tsum G eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff tsum G eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1806-L1811
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1806-L1811

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tsum_G_eq_zero (j d : ℕ) : letI := piTop;
    (PowerSeries.coeff d) (∑' ℓ : ℕ,
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by sorry
