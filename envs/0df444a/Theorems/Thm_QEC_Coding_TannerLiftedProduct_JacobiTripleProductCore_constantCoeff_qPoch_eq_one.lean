-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_qPoch_eq_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_qPoch_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:38.345392+00:00
-- url     : https://prove2.me/theorems/5aea7a0f-e0d1-492c-920c-cf8f2a6d6ff1
-- title:
--   Jacobi Triple Product Core: constant Coeff q Poch eq one
-- statement:
--   The Jacobi Triple Product Core construction uses the constant Coeff q Poch eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L349-L351
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L349-L351

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_qPoch_eq_one (k : ℕ) :
    PowerSeries.constantCoeff (qPoch (q ^ 2) (q ^ 2) k : R) = 1 := by sorry
