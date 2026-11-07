-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_W_term_coeff_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_term_coeff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:20.18669+00:00
-- url     : https://prove2.me/theorems/c4afa5e6-df4c-4e2f-8a15-2efa84ae2e36
-- title:
--   Jacobi Triple Product Core: W term coeff eq
-- statement:
--   The Jacobi Triple Product Core construction uses the W term coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1626-L1631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1626-L1631

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.W_term_coeff_eq (j ℓ : ℕ) (b : ℤ) :
    ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ *
      (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ + ℓ.choose 2))) := by sorry
