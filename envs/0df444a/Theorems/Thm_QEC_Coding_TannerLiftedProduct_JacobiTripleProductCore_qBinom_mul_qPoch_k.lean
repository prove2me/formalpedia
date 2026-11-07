-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch_k
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:50.402201+00:00
-- url     : https://prove2.me/theorems/d65ef5e8-6ea1-40db-aa04-a4adfc6576b6
-- title:
--   Jacobi Triple Product Core: q Binom mul q Poch k
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom mul q Poch k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L508-L515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L508-L515

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_k (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k * qPoch (q ^ 2) (q ^ 2) k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k := by sorry
