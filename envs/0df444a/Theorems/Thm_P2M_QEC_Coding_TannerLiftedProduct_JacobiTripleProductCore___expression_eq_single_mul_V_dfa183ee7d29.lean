-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:49.750433+00:00
-- url     : https://prove2.me/theorems/7fd5dccd-171c-49d8-b5d1-77d21d174413
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   expression eq single mul V dfa183ee7d29: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   expression eq single mul
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   expression eq single mul V dfa183ee7d29 construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   expression eq single mul V dfa183ee7d29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1764-L1773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1764-L1773

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29 (j ℓ : ℕ) :
    let N_val := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ
    ι_hahn ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    HahnSeries.single (↑N_val : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) * V ℓ := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«ι_expression_eq_single_mul_V» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29
