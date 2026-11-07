-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exists_bound_for_order
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_bound_for_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:39.799055+00:00
-- url     : https://prove2.me/theorems/00f1f279-e1b3-413d-ada5-2d24d0de095b
-- title:
--   Jacobi Triple Product Core: exists bound for order
-- statement:
--   The Jacobi Triple Product Core construction uses the exists bound for order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L770-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L770-L773

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_bound_for_order
    {f : ℕ → ℕ∞} (hf : Filter.Tendsto f Filter.atTop (nhds ⊤)) (d : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (d : ℕ∞) < f n := by sorry
