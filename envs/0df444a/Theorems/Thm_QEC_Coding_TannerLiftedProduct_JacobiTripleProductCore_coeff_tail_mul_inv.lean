-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tail_mul_inv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tail_mul_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:07.278418+00:00
-- url     : https://prove2.me/theorems/fef01f4f-be89-455b-90f5-b37ccd7ebc06
-- title:
--   Jacobi Triple Product Core: coeff tail mul inv
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff tail mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L480-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L480-L485

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tail_mul_inv (m k n : ℕ) (hn : m + k + 1 ≤ n) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
