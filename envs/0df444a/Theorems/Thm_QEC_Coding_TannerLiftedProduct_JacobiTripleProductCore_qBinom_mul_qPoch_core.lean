-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch_core
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:25.260926+00:00
-- url     : https://prove2.me/theorems/0545d6b0-7bac-488d-b927-15a3d89cc32b
-- title:
--   Jacobi Triple Product Core: q Binom mul q Poch core
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom mul q Poch core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L419-L433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L419-L433

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_core (Q : R) (n k : ℕ) (hk : k < n)
    (ih1 : qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n)
    (ih2 : qBinom Q n (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - (k + 1)) = qPoch Q Q n) :
    (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) *
      (qPoch Q Q k * (1 - Q * Q ^ k)) *
      (qPoch Q Q (n - (k + 1)) * (1 - Q * Q ^ (n - (k + 1)))) =
    qPoch Q Q n * (1 - Q * Q ^ n) := by sorry
