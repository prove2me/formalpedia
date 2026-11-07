-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:59.44031+00:00
-- url     : https://prove2.me/theorems/29783400-413b-4e33-90ec-b4e6a3bd5790
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   neg one pow 23465ab75a05: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   neg one pow 23465ab75a05
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   neg one pow 23465ab75a05 construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   neg one pow 23465ab75a05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1510-L1517
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1510-L1517

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05 (ℓ : ℕ) :
    ι_hahn ((-1 : R) ^ ℓ) = HahnSeries.single (0 : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«ι_neg_one_pow» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05
