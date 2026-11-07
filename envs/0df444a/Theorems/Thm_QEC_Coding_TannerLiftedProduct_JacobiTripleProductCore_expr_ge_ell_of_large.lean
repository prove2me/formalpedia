-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_expr_ge_ell_of_large
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expr_ge_ell_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:05.442026+00:00
-- url     : https://prove2.me/theorems/a0e65d24-14b0-485f-b6a5-9d4c8b006e10
-- title:
--   Jacobi Triple Product Core: expr ge ell of large
-- statement:
--   The Jacobi Triple Product Core construction uses the expr ge ell of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1581-L1590
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1581-L1590

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.expr_ge_ell_of_large (j ℓ : ℕ) (hℓ : 2 * j + 2 ≤ ℓ) :
    (ℓ : ℤ) ≤ -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) := by sorry
