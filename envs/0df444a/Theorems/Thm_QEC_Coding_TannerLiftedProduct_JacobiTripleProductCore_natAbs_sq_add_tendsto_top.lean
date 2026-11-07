-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_natAbs_sq_add_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.natAbs_sq_add_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:54.660333+00:00
-- url     : https://prove2.me/theorems/bdf293ac-ac73-4e3a-9cfd-11ef31e11a30
-- title:
--   Jacobi Triple Product Core: nat Abs sq add tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the nat Abs sq add tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1433-L1437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1433-L1437

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.natAbs_sq_add_tendsto_top (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞))
      Filter.atTop (nhds ⊤) := by sorry
