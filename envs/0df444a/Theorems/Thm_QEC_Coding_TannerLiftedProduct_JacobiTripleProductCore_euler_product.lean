-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_product
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:45.139196+00:00
-- url     : https://prove2.me/theorems/79b6aaa4-56a5-450b-9ec5-83363b388739
-- title:
--   Jacobi Triple Product Core: euler product
-- statement:
--   The Jacobi Triple Product Core construction uses the euler product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L594-L598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L594-L598

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_product (x : R) : letI := piTop;
    qPochhammerInf (-x * q) (q ^ 2) =
    ∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 := by sorry
