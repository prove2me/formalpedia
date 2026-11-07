-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_neg_factor_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_factor_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:53.086972+00:00
-- url     : https://prove2.me/theorems/7c6072e9-6aa7-4caa-b3f9-ca653bb4d772
-- title:
--   Jacobi Triple Product Core: order neg factor tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the order neg factor tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L219-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L219-L222

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_factor_tendsto_top (x : R) : letI := piTop;
    Filter.Tendsto (fun i => ((-x * q) * (q ^ 2) ^ i).order) Filter.atTop (nhds ⊤) := by sorry
