-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_T_finite_support
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.T_finite_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:10.67814+00:00
-- url     : https://prove2.me/theorems/07d29769-beaf-481d-8791-2d058faed7a8
-- title:
--   Jacobi Triple Product Core: T finite support
-- statement:
--   The Jacobi Triple Product Core construction uses the T finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1609-L1613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1609-L1613

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.T_finite_support (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite := by sorry
