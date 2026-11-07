-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_antidiag_to_range_sum
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_to_range_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:15.7454+00:00
-- url     : https://prove2.me/theorems/db2c1feb-40ba-4081-84f7-b69a0afaffe1
-- title:
--   Jacobi Triple Product Core: antidiag to range sum
-- statement:
--   The Jacobi Triple Product Core construction uses the antidiag to range sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L687-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L687-L694

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_to_range_sum {n : ℕ} :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    ∑ k ∈ Finset.range (n + 1), aCoeff (n - k) * bCoeff k := by sorry
