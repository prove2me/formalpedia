-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_coeff_eq_ite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_coeff_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:17.238403+00:00
-- url     : https://prove2.me/theorems/4c087a4f-8481-4c26-ad61-e69a65357829
-- title:
--   Jacobi Triple Product Core: tail coeff eq ite
-- statement:
--   The Jacobi Triple Product Core construction uses the tail coeff eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L293-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L293-L298

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_coeff_eq_ite (x : R) (m n k : ℕ) (hmn : m < n) (j : ℕ) (hj : j ≤ m) :
    (qPoch ((-x * q) * (q ^ 2) ^ n) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by sorry
