-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_termwise_coeff_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.termwise_coeff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:54.519187+00:00
-- url     : https://prove2.me/theorems/0923e24c-ad46-46e4-be1d-1cdfa7de3dfc
-- title:
--   Jacobi Triple Product Core: termwise coeff eq
-- statement:
--   The Jacobi Triple Product Core construction uses the termwise coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L564-L569
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L564-L569

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.termwise_coeff_eq (x : R) (m k : ℕ) (hk : k ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    (q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by sorry
