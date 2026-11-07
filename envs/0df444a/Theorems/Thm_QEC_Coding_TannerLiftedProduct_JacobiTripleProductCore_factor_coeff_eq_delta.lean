-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_coeff_eq_delta
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:23.930195+00:00
-- url     : https://prove2.me/theorems/9ae26438-bc60-4a84-9e4e-48ec368e1ad8
-- title:
--   Jacobi Triple Product Core: factor coeff eq delta
-- statement:
--   The Jacobi Triple Product Core construction uses the factor coeff eq delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L461-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L461-L466

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_delta (m d : ℕ) (hd : m + 2 ≤ d) (j : ℕ) (hj : j ≤ m) :
    ((1 - (q : R) ^ (2 * d)) : R).coeff j = if j = 0 then 1 else 0 := by sorry
