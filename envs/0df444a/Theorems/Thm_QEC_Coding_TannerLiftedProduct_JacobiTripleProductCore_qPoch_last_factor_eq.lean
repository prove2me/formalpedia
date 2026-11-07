-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_last_factor_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_last_factor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:14.472532+00:00
-- url     : https://prove2.me/theorems/13e9abe4-258d-4cb4-b189-f5c98af6352f
-- title:
--   Jacobi Triple Product Core: q Poch last factor eq
-- statement:
--   The Jacobi Triple Product Core construction uses the q Poch last factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1519-L1521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1519-L1521

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_last_factor_eq (ℓ : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ ℓ = 1 - q ^ (2 * (↑ℓ + 1)) := by sorry
