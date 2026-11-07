-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_eq_finite_sum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_eq_finite_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:11.718349+00:00
-- url     : https://prove2.me/theorems/2f12139a-cfc4-4a65-a873-d08ebed336c8
-- title:
--   Jacobi Triple Product Core: lhs eq finite sum
-- statement:
--   The Jacobi Triple Product Core construction uses the lhs eq finite sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1008-L1017
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1008-L1017

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_eq_finite_sum (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by sorry
