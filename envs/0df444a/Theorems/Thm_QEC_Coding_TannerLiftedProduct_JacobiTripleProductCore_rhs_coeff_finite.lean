-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_coeff_finite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_coeff_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:18.304691+00:00
-- url     : https://prove2.me/theorems/1144e24d-872d-40b4-90a4-edbf07689102
-- title:
--   Jacobi Triple Product Core: rhs coeff finite
-- statement:
--   The Jacobi Triple Product Core construction uses the rhs coeff finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L378-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L378-L390

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_coeff_finite (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
