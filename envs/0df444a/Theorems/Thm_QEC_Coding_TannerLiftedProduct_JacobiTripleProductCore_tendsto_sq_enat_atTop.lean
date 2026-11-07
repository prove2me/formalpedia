-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tendsto_sq_enat_atTop
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tendsto_sq_enat_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:14.694045+00:00
-- url     : https://prove2.me/theorems/1d10af7a-5f3a-430e-b411-b7deddf5ecc3
-- title:
--   Jacobi Triple Product Core: tendsto sq enat at Top
-- statement:
--   The Jacobi Triple Product Core construction uses the tendsto sq enat at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L365-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L365-L370

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tendsto_sq_enat_atTop :
    Filter.Tendsto (fun k : ℕ => (↑(k ^ 2) : ℕ∞)) Filter.atTop (nhds ⊤) := by sorry
