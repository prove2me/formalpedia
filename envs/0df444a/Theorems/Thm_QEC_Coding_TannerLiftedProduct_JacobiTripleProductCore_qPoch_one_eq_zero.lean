-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_one_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_one_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:07.944207+00:00
-- url     : https://prove2.me/theorems/f7d55d75-e439-402a-8763-8e0a8119da70
-- title:
--   Jacobi Triple Product Core: q Poch one eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the q Poch one eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L640-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L640-L641

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_one_eq_zero (Q : R) {n : ℕ} (hn : 0 < n) : qPoch 1 Q n = 0 := by sorry
