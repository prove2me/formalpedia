-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_E_terms
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_E_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:27.937691+00:00
-- url     : https://prove2.me/theorems/3551a799-7ed2-4948-8852-4567c225e470
-- title:
--   Jacobi Triple Product Core: summable E terms
-- statement:
--   The Jacobi Triple Product Core construction uses the summable E terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1309-L1313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1309-L1313

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_E_terms : letI := piTop;
    Summable (fun ℓ : ℕ => (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by sorry
