-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_two_mul_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_two_mul_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:47.305417+00:00
-- url     : https://prove2.me/theorems/95a25abf-dbec-4452-9b51-fcfeb40e51ad
-- title:
--   Jacobi Triple Product Core: enat two mul tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the enat two mul tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L207-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L207-L212

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_two_mul_tendsto_top :
    Filter.Tendsto (fun i : ℕ => 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) := by sorry
