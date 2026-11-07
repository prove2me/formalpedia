-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:10.228066+00:00
-- url     : https://prove2.me/theorems/deec6e22-4df4-4209-84ef-3a0a1730f2fb
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A Q  pow fc719b7707f4: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A Q  pow fc719b7707f4
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A Q  pow fc719b7707f4 construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core neg A Q  pow fc719b7707f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1550-L1551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1550-L1551

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4 (j ℓ : ℕ) :
    (-(A_hahn j * Q₀)) ^ ℓ = (-A_hahn j) ^ ℓ * Q₀ ^ ℓ := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«neg_A_Q₀_pow» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4
