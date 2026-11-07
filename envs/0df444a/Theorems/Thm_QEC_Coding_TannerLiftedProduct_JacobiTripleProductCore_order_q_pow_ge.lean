-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_q_pow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:00.259205+00:00
-- url     : https://prove2.me/theorems/b7266d5f-e29c-4bbb-8b6c-3cc334159a42
-- title:
--   Jacobi Triple Product Core: order q pow ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order q pow ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L196-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L196-L196

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_q_pow_ge (m : ℕ) : (m : ℕ∞) ≤ (q ^ m : R).order := by sorry
