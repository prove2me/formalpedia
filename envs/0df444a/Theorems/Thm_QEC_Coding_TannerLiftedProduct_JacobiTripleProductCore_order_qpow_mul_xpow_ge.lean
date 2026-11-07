-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_qpow_mul_xpow_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_qpow_mul_xpow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:10.472774+00:00
-- url     : https://prove2.me/theorems/9ba0b69a-ca13-4040-ba00-dcb871d9b7f9
-- title:
--   Jacobi Triple Product Core: order qpow mul xpow ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order qpow mul xpow ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L487-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L487-L489

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_qpow_mul_xpow_ge (x : R) (k : ℕ) :
    (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) * x ^ k : R).order := by sorry
