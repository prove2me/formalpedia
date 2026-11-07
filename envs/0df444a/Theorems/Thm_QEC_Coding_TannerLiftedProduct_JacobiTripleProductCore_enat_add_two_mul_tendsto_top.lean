-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_add_two_mul_tendsto_top
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_add_two_mul_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:12.128489+00:00
-- url     : https://prove2.me/theorems/8e5524f9-ddb4-4467-973a-77fda4b8c98a
-- title:
--   Jacobi Triple Product Core: enat add two mul tendsto top
-- statement:
--   The Jacobi Triple Product Core construction uses the enat add two mul tendsto top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L214-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L214-L217

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_add_two_mul_tendsto_top (c : ℕ∞) :
    Filter.Tendsto (fun i : ℕ => c + 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) := by sorry
