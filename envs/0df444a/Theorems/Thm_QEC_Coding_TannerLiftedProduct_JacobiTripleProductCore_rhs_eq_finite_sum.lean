-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_eq_finite_sum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_eq_finite_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:33.247568+00:00
-- url     : https://prove2.me/theorems/57c8eac2-ba8d-4960-87c0-17aeff1a0569
-- title:
--   Jacobi Triple Product Core: rhs eq finite sum
-- statement:
--   The Jacobi Triple Product Core construction uses the rhs eq finite sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L991-L1006
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L991-L1006

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_eq_finite_sum (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by sorry
