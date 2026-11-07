-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_qPoch_coeff_eq_ite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_qPoch_coeff_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:39.520669+00:00
-- url     : https://prove2.me/theorems/a8181ada-1fa2-473f-80c1-36891b91632b
-- title:
--   Jacobi Triple Product Core: tail q Poch coeff eq ite
-- statement:
--   The Jacobi Triple Product Core construction uses the tail q Poch coeff eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L468-L478
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L468-L478

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_qPoch_coeff_eq_ite (m k n : ℕ) (hn : m + k + 1 ≤ n) (j : ℕ) (hj : j ≤ m) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by sorry
