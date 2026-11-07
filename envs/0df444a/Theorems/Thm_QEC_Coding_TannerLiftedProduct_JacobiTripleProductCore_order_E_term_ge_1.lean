-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_E_term_ge_1
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_E_term_ge_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:55.585799+00:00
-- url     : https://prove2.me/theorems/babb7c90-5200-47d6-b097-6f5f16285ae3
-- title:
--   Jacobi Triple Product Core: order E term ge 1
-- statement:
--   The Jacobi Triple Product Core construction uses the order E term ge 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1302-L1307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1302-L1307

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_E_term_ge_1 (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by sorry
