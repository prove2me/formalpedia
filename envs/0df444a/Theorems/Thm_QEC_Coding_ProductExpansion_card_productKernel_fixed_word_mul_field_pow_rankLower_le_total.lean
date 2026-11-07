-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
-- name    : QEC.Coding.ProductExpansion.card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:09.031944+00:00
-- url     : https://prove2.me/theorems/2fe2aa67-db12-46ec-8bb4-0f85ed219431
-- title:
--   Product Expansion: card product Kernel fixed word mul field pow rank Lower le total
-- statement:
--   Replacing the exact syndrome rank by any certified lower bound only
--   weakens the finite counting penalty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L942-L959
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L942-L959

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
    (h' : Matrix R' W F) (x : Matrix W W F) (k : Nat)
    (hk : k ≤ (h' * x).rank) :
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card (Matrix R W F) := by sorry
