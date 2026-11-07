-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_eq_tail_mul_inv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_eq_tail_mul_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:15.739958+00:00
-- url     : https://prove2.me/theorems/8c710524-d6bd-44e2-8294-51f9643a23f4
-- title:
--   Jacobi Triple Product Core: q Binom eq tail mul inv
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom eq tail mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L517-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L517-L524

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_eq_tail_mul_inv (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 := by sorry
