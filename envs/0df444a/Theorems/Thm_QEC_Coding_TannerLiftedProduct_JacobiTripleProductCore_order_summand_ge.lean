-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_summand_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_summand_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:28.041338+00:00
-- url     : https://prove2.me/theorems/d5610e41-9135-44b4-ac21-93cee2ab71ae
-- title:
--   Jacobi Triple Product Core: order summand ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order summand ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1152-L1165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1152-L1165

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_summand_ge (k ℓ : ℕ) :
    ((k + ℓ) ^ 2 + ℓ : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by sorry
