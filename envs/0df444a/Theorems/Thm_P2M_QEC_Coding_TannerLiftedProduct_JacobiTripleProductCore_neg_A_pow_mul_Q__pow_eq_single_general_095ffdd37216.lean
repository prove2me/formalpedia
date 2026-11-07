-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:15.058191+00:00
-- url     : https://prove2.me/theorems/d2ec90fa-e05f-487c-bc91-3200ef1cba76
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single general 095ffdd37216: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single general 095ffdd37216 construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A pow mul Q  pow eq single general 095ffdd37216 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1615-L1620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1615-L1620

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216 (j ℓ n : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ n =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑n : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«neg_A_pow_mul_Q₀_pow_eq_single_general» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_pow_mul_Q__pow_eq_single_general_095ffdd37216
