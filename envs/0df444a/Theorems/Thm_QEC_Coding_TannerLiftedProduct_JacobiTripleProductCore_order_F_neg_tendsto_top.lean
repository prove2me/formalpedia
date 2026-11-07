-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_F_neg_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_neg_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:58.50964+00:00
-- url     : https://prove2.me/theorems/4a0b93f0-3f3d-4ffc-b8db-11671a775969
-- title:
--   Jacobi Triple Product Core: order F neg tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the order F neg tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1439-L1443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1439-L1443

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_neg_tendsto_top (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => (F (-(↑j + 1), ℓ)).order)
      Filter.atTop (nhds ⊤) := by sorry
