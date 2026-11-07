-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_qBinom_eq_coeff_inv_on_antidiag
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_qBinom_eq_coeff_inv_on_antidiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:52.412204+00:00
-- url     : https://prove2.me/theorems/3a56d39e-58fa-426d-a605-a26e0d76f528
-- title:
--   Jacobi Triple Product Core: coeff q Binom eq coeff inv on antidiag
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff q Binom eq coeff inv on antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L539-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L539-L546

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_qBinom_eq_coeff_inv_on_antidiag (m k i j : ℕ) (hk : k ≤ m)
    (hij : i + j = m) (_hj : k ^ 2 ≤ j) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by sorry
