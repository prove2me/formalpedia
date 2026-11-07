-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factors_multipliable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factors_multipliable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:05.929797+00:00
-- url     : https://prove2.me/theorems/a15d978e-43aa-4aba-8130-9f1c435c0650
-- title:
--   Jacobi Triple Product Core: factors multipliable
-- statement:
--   The Jacobi Triple Product Core construction uses the factors multipliable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L230-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L230-L237

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factors_multipliable (x : R) : letI := piTop;
    Multipliable (fun i => 1 - (-x * q) * (q ^ 2) ^ i : ℕ → R) := by sorry
