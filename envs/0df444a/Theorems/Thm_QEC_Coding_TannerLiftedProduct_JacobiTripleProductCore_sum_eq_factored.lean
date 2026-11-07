-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_sum_eq_factored
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_eq_factored
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:19.03921+00:00
-- url     : https://prove2.me/theorems/863f473e-d84f-4b6d-818f-9bdbf21a6e28
-- title:
--   Jacobi Triple Product Core: sum eq factored
-- statement:
--   The Jacobi Triple Product Core construction uses the sum eq factored property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L696-L703
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L696-L703

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.sum_eq_factored {n : ℕ} :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2 := by sorry
