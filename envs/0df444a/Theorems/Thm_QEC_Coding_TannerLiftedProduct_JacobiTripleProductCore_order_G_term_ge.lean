-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_G_term_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_G_term_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:58.254636+00:00
-- url     : https://prove2.me/theorems/65ffcfbd-cb25-4cc0-87f8-7b44e75dc9fc
-- title:
--   Jacobi Triple Product Core: order G term ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order G term ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1458-L1469
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1458-L1469

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_G_term_ge (j ℓ : ℕ) :
    (N_exp j ℓ : ℕ∞) ≤
    ((-1 : R) ^ ℓ * q ^ N_exp j ℓ *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by sorry
