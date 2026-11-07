-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_coeff_mul_pow_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_coeff_mul_pow_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:27.433021+00:00
-- url     : https://prove2.me/theorems/1f8295ba-befb-4c62-919a-a8511f63efb1
-- title:
--   Jacobi Triple Product Core: order coeff mul pow ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order coeff mul pow ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L732-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L732-L739

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_coeff_mul_pow_ge {x : R} (hx : x.constantCoeff = 0) (p : S) (n : ℕ) :
    (n : ℕ∞) ≤ ((p.coeff n) * x ^ n).order := by sorry
