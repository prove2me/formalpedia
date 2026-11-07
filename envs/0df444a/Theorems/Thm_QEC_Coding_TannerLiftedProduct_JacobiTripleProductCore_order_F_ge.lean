-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_F_ge
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:50.61112+00:00
-- url     : https://prove2.me/theorems/cbbe56e2-4909-43ff-a68e-1bb6b22aa826
-- title:
--   Jacobi Triple Product Core: order F ge
-- statement:
--   The Jacobi Triple Product Core construction uses the order F ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1424-L1431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1424-L1431

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_ge (z : ℤ) (ℓ : ℕ) :
    ((z + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞) ≤ (F (z, ℓ)).order := by sorry
