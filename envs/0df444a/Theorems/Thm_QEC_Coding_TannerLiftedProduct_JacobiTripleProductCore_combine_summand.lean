-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_combine_summand
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_summand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:32.259383+00:00
-- url     : https://prove2.me/theorems/140a9e9e-7568-4859-a8b4-def470add623
-- title:
--   Jacobi Triple Product Core: combine summand
-- statement:
--   The Jacobi Triple Product Core construction uses the combine summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L131-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L131-L136

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_summand (A Q : R) (n k : ℕ) :
    qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 +
    qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by sorry
