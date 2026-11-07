-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_expand_shifted_product
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expand_shifted_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:42.146169+00:00
-- url     : https://prove2.me/theorems/f399db36-6de4-4f18-9ada-087c3280a412
-- title:
--   Jacobi Triple Product Core: expand shifted product
-- statement:
--   The Jacobi Triple Product Core construction uses the expand shifted product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1056-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1056-L1069

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expand_shifted_product (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) =
    ∑' ℓ : ℕ, (-1) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by sorry
