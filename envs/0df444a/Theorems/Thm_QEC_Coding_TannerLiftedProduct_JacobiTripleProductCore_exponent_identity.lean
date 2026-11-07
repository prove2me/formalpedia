-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_identity
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:45.0863+00:00
-- url     : https://prove2.me/theorems/3b8f9db4-4b60-4303-b6e2-b0a83afaaa9b
-- title:
--   Jacobi Triple Product Core: exponent identity
-- statement:
--   The Jacobi Triple Product Core construction uses the exponent identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1759-L1762
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1759-L1762

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity (j ℓ : ℕ) :
    ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℤ) =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by sorry
