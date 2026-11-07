-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:41.806718+00:00
-- url     : https://prove2.me/theorems/2ebb9b90-1f19-4153-baf5-33829f037626
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core q Poch succ  251408f0b858: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core q Poch succ  251408f0b858
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core q Poch succ  251408f0b858 construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core q Poch succ  251408f0b858 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L392-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L392-L394

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858 {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) :
    qPoch A Q (n + 1) = qPoch A Q n * (1 - A * Q ^ n) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«qPoch_succ'» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
