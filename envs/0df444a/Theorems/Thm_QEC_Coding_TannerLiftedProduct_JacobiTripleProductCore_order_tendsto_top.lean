-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:24.657846+00:00
-- url     : https://prove2.me/theorems/a288b5ee-6913-4e47-b55f-c6b3779f7961
-- title:
--   Jacobi Triple Product Core: order tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the order tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L741-L747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L741-L747

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_tendsto_top {x : R} (hx : x.constantCoeff = 0) (p : S) :
    Filter.Tendsto (fun n : ℕ => ((p.coeff n) * x ^ n).order) Filter.atTop (nhds ⊤) := by sorry
