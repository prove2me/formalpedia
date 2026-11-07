-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:08.036042+00:00
-- url     : https://prove2.me/theorems/8bddc760-6434-42ef-b331-27d276b1b2f2
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single f8efc88f6b2b: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq s
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single f8efc88f6b2b construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single f8efc88f6b2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1560-L1565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1560-L1565

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b (j ℓ : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«neg_A_pow_mul_Q₀_pow_eq_single» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_f8efc88f6b2b
