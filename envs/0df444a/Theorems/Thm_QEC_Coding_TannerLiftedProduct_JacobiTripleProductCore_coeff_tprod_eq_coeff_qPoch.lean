-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tprod_eq_coeff_qPoch
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tprod_eq_coeff_qPoch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:07.863533+00:00
-- url     : https://prove2.me/theorems/9452cc96-04cc-45e0-9ae9-78ca0b13681b
-- title:
--   Jacobi Triple Product Core: coeff tprod eq coeff q Poch
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff tprod eq coeff q Poch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L307-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L307-L316

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tprod_eq_coeff_qPoch (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    ((∏' i, (1 - (-x * q) * (q ^ 2) ^ i : R)) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by sorry
