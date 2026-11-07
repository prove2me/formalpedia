-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_convolution_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.convolution_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:19.318375+00:00
-- url     : https://prove2.me/theorems/0a28b9d5-f62b-4ffe-8705-df5f64e6a834
-- title:
--   Jacobi Triple Product Core: convolution eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the convolution eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L705-L711
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L705-L711

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.convolution_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      aCoeff p.1 * bCoeff p.2 = 0 := by sorry
