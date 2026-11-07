-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_coeff_eq_invOfUnit
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:50.162262+00:00
-- url     : https://prove2.me/theorems/12e17373-d23d-4b52-add0-ccaa4b1e32cb
-- title:
--   Jacobi Triple Product Core: q Binom coeff eq inv Of Unit
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom coeff eq inv Of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L526-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L526-L530

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit (m k n : ℕ) (_ : k ≤ m) (hn : m + k + 1 ≤ n) :
    (qBinom (q ^ 2) n k : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
