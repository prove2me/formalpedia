-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_eval_series
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_eval_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:29.617699+00:00
-- url     : https://prove2.me/theorems/b0fab15e-a936-4530-9ca9-85d02c6f1fad
-- title:
--   Jacobi Triple Product Core: summable eval series
-- statement:
--   The Jacobi Triple Product Core construction uses the summable eval series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L749-L752
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L749-L752

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_eval_series {x : R} (hx : x.constantCoeff = 0) (p : S) :
    letI := piTop; Summable (fun n => p.coeff n * x ^ n) := by sorry
