-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factor_shift_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_shift_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:49.047481+00:00
-- url     : https://prove2.me/theorems/eb3db600-1b7d-4bbf-9b46-2b63987748e8
-- title:
--   Jacobi Triple Product Core: factor shift eq
-- statement:
--   The Jacobi Triple Product Core construction uses the factor shift eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L888-L889
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L888-L889

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_shift_eq (n k : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ (n + k) = 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n := by sorry
