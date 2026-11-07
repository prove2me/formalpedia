-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_identity_algebraic
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity_algebraic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:44.643939+00:00
-- url     : https://prove2.me/theorems/62a33720-500f-4546-94b0-d372c29f7695
-- title:
--   Jacobi Triple Product Core: exponent identity algebraic
-- statement:
--   The Jacobi Triple Product Core construction uses the exponent identity algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1745-L1757
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1745-L1757

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity_algebraic (j ℓ : ℕ) :
    (↑ℓ - (↑j + 1 : ℤ)) ^ 2 + ↑ℓ =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by sorry
