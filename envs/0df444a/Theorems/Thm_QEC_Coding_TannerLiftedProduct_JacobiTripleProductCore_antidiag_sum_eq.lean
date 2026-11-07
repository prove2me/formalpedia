-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_antidiag_sum_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:01.84192+00:00
-- url     : https://prove2.me/theorems/9db15adc-57cd-433f-ba3a-b5cd3530ac7c
-- title:
--   Jacobi Triple Product Core: antidiag sum eq
-- statement:
--   The Jacobi Triple Product Core construction uses the antidiag sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L258-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L258-L267

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_sum_eq (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      f.coeff p.1 * g.coeff p.2 = f.coeff m := by sorry
