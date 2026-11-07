-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_conv_sum_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.conv_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:00.339224+00:00
-- url     : https://prove2.me/theorems/5c3d89a7-7033-4b32-8117-2262b605f2bb
-- title:
--   Jacobi Triple Product Core: conv sum eq
-- statement:
--   The Jacobi Triple Product Core construction uses the conv sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L548-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L548-L562

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.conv_sum_eq (x : R) (m k : ℕ) (hk : k ≤ m) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (qBinom (q ^ 2) (2 * m + 1) k : R).coeff p.1 * (q ^ (k ^ 2) * x ^ k).coeff p.2 =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff p.1 *
      (q ^ (k ^ 2) * x ^ k).coeff p.2 := by sorry
