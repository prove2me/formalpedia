-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_shifted_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_shifted_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:52.918984+00:00
-- url     : https://prove2.me/theorems/0e6761de-9e1b-4934-8acf-630b3f81d424
-- title:
--   Jacobi Triple Product Core: order shifted tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the order shifted tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L896-L906
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L896-L906

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_shifted_tendsto_top (k : ℕ) :
    Filter.Tendsto (fun n ↦ (q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n).order)
      Filter.atTop (nhds ⊤) := by sorry
