-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_extract_sign
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.extract_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:26.383544+00:00
-- url     : https://prove2.me/theorems/340c55df-0443-4249-8239-ac728954f623
-- title:
--   Jacobi Triple Product Core: extract sign
-- statement:
--   The Jacobi Triple Product Core construction uses the extract sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1051-L1054
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1051-L1054

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.extract_sign (k ℓ : ℕ) :
    (-q ^ (2 * k + 1)) ^ ℓ = (-1) ^ ℓ * q ^ (ℓ * (2 * k + 1)) := by sorry
