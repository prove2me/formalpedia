-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_exponent_le
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:12.356727+00:00
-- url     : https://prove2.me/theorems/6095cb44-36f2-4f8e-b4b2-6ff8aa70240b
-- title:
--   Jacobi Triple Product Core: finite exponent le
-- statement:
--   The Jacobi Triple Product Core construction uses the finite exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1592-L1599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1592-L1599

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_exponent_le (j : ℕ) (b : ℤ) :
    {ℓ : ℕ | -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) ≤ b}.Finite := by sorry
