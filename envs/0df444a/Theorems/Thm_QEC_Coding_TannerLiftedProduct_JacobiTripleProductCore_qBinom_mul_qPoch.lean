-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:57.766433+00:00
-- url     : https://prove2.me/theorems/b21853f0-4aa8-4fcf-b66c-f3a750cc0a3a
-- title:
--   Jacobi Triple Product Core: q Binom mul q Poch
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom mul q Poch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L445-L459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L445-L459

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch (Q : R) (n k : ℕ) (hkn : k ≤ n) :
    qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n := by sorry
