-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_W_finite_support
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:26.911985+00:00
-- url     : https://prove2.me/theorems/554506bc-08e5-4d7e-9cdd-c26bbaa74dd1
-- title:
--   Jacobi Triple Product Core: W finite support
-- statement:
--   The Jacobi Triple Product Core construction uses the W finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1633-L1639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1633-L1639

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_finite_support (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite := by sorry
