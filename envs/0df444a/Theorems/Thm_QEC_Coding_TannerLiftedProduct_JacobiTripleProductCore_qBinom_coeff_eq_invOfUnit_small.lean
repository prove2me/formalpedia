-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_coeff_eq_invOfUnit_small
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:54.335337+00:00
-- url     : https://prove2.me/theorems/2866629c-37d6-4604-a65c-261f31eb8391
-- title:
--   Jacobi Triple Product Core: q Binom coeff eq inv Of Unit small
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom coeff eq inv Of Unit small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L532-L537
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L532-L537

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit_small (m k i : ℕ) (hk : k ≤ m) (hi : i < k)
    (_him : i ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by sorry
