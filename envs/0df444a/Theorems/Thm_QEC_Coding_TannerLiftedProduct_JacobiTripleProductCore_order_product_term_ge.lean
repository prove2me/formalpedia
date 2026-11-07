-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_product_term_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_product_term_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:32.387513+00:00
-- url     : https://prove2.me/theorems/f114adf3-a28a-448c-bf71-49c5488bd4fa
-- title:
--   Jacobi Triple Product Core: order product term ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order product term ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1315-L1324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1315-L1324

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_product_term_ge (m : ℤ) (ℓ : ℕ) :
    (m.natAbs ^ 2 + ℓ : ℕ∞) ≤
      ((PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
       ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).order := by sorry
