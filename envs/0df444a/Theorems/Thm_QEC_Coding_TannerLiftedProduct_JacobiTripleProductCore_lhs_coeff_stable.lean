-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_coeff_stable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_coeff_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:20.889635+00:00
-- url     : https://prove2.me/theorems/b7fbf5ce-ad84-4275-a94f-f514c02b243a
-- title:
--   Jacobi Triple Product Core: lhs coeff stable
-- statement:
--   The Jacobi Triple Product Core construction uses the lhs coeff stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L318-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L318-L323

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_coeff_stable (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    (qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by sorry
