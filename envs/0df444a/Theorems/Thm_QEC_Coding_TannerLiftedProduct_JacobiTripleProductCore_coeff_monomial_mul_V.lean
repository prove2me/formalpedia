-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_monomial_mul_V
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_monomial_mul_V
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:08.509321+00:00
-- url     : https://prove2.me/theorems/1ff94aed-640b-44ae-ad9e-f05402f6ec51
-- title:
--   Jacobi Triple Product Core: coeff monomial mul V
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff monomial mul V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1601-L1607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1601-L1607

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_monomial_mul_V (j ℓ : ℕ) (b : ℤ) :
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ * (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2))) := by sorry
