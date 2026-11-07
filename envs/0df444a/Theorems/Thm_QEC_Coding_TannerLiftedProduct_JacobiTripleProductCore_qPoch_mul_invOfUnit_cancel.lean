-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_mul_invOfUnit_cancel
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_mul_invOfUnit_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:37.876201+00:00
-- url     : https://prove2.me/theorems/f38051b9-ff85-4a02-9701-48948df698f0
-- title:
--   Jacobi Triple Product Core: q Poch mul inv Of Unit cancel
-- statement:
--   The Jacobi Triple Product Core construction uses the q Poch mul inv Of Unit cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L500-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L500-L502

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_mul_invOfUnit_cancel (k : ℕ) :
    qPoch (q ^ 2) (q ^ 2) k * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 = 1 := by sorry
