-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inner_sum_summable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inner_sum_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:48.592424+00:00
-- url     : https://prove2.me/theorems/a443de6d-5c0c-4e39-962a-54ee0ad11da1
-- title:
--   Jacobi Triple Product Core: inner sum summable
-- statement:
--   The Jacobi Triple Product Core construction uses the inner sum summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1445-L1448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1445-L1448

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inner_sum_summable (j : ℕ) : letI := piTop;
    Summable (fun ℓ : ℕ => F (-(↑j + 1), ℓ)) := by sorry
