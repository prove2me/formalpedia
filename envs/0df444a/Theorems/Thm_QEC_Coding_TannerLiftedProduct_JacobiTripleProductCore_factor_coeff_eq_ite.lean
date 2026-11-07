-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_coeff_eq_ite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:51.807258+00:00
-- url     : https://prove2.me/theorems/b42d17e7-9a0e-46d9-94cc-6862b3ecd4a0
-- title:
--   Jacobi Triple Product Core: factor coeff eq ite
-- statement:
--   The Jacobi Triple Product Core construction uses the factor coeff eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L251-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L251-L256

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_ite (x : R) (j i : ℕ) (hji : j < 1 + 2 * i) :
    (1 - (-x * q) * (q ^ 2) ^ i : R).coeff j = if j = 0 then 1 else 0 := by sorry
