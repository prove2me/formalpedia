-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_neg_q_aI_pow_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_q_aI_pow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:23.836662+00:00
-- url     : https://prove2.me/theorems/1ac7875a-9109-4e00-be64-0604e620804e
-- title:
--   Jacobi Triple Product Core: order neg q a I pow ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order neg q a I pow ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1292-L1300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1292-L1300

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_q_aI_pow_ge (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ : R).order := by sorry
