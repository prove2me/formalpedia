-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_inverse
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:45.763246+00:00
-- url     : https://prove2.me/theorems/f5566307-4e5c-4994-8e97-0208257069a7
-- title:
--   Jacobi Triple Product Core: euler inverse
-- statement:
--   The Jacobi Triple Product Core construction uses the euler inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L879-L886
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L879-L886

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.euler_inverse (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    (∑' ℓ : ℕ, (-x) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) *
    qPochhammerInf (-x) (q ^ 2) = 1 := by sorry
