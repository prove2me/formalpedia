-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_eq_zero_of_order_gt
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_eq_zero_of_order_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:39.084233+00:00
-- url     : https://prove2.me/theorems/cb51a462-f0af-43a1-ab17-91ef70b26156
-- title:
--   Jacobi Triple Product Core: coeff mul eq zero of order gt
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff mul eq zero of order gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L775-L783
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L775-L783

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_eq_zero_of_order_gt {d : ℕ} {φ ψ : R}
    (h : (d : ℕ∞) < φ.order ∨ (d : ℕ∞) < ψ.order) :
    (PowerSeries.coeff d) (φ * ψ) = 0 := by sorry
