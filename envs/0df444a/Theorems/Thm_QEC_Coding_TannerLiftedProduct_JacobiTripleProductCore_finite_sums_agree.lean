-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_sums_agree
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_sums_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:58.169603+00:00
-- url     : https://prove2.me/theorems/b7ac3974-3637-413a-8911-31019a27e688
-- title:
--   Jacobi Triple Product Core: finite sums agree
-- statement:
--   The Jacobi Triple Product Core construction uses the finite sums agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L571-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L571-L582

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_sums_agree (x : R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1 + 1),
      (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
