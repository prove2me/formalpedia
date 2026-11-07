-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_first_factor_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_first_factor_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:47.722465+00:00
-- url     : https://prove2.me/theorems/73b694fa-953e-4b7a-be06-c740b72a51fb
-- title:
--   Jacobi Triple Product Core: order first factor ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order first factor ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1255-L1262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1255-L1262

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_first_factor_ge (m : ℤ) :
    (m.natAbs ^ 2 : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order := by sorry
