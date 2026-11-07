-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_lower_bound
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:50.879283+00:00
-- url     : https://prove2.me/theorems/3d8a4aa8-afe1-4bc9-81de-022380a62d2d
-- title:
--   Jacobi Triple Product Core: order lower bound
-- statement:
--   The Jacobi Triple Product Core construction uses the order lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L198-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L198-L205

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_lower_bound (x : R) (i : ℕ) :
    (-x * q).order + 2 * i ≤ ((-x * q) * (q ^ 2) ^ i).order := by sorry
