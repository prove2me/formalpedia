-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_product_coeff
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_product_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:03.924207+00:00
-- url     : https://prove2.me/theorems/80b94072-ba2a-434a-addb-ad1d8132cd2c
-- title:
--   Jacobi Triple Product Core: euler product coeff
-- statement:
--   The Jacobi Triple Product Core construction uses the euler product coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L584-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L584-L592

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_product_coeff (x : R) (m : ℕ) :
    letI := piTop
    (qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
