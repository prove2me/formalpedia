-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_productKernel_fixed_word_mul_field_pow_rank_eq_total
-- name    : QEC.Coding.ProductExpansion.card_productKernel_fixed_word_mul_field_pow_rank_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:03.652482+00:00
-- url     : https://prove2.me/theorems/623bcdf8-c0f8-43c6-86c9-8fa39d7eedb4
-- title:
--   Product Expansion: card product Kernel fixed word mul field pow rank eq total
-- statement:
--   For a fixed candidate product word `x`, the exact PK22 constraint
--   penalty is the rank of its left syndrome `h' * x` times the number of
--   independently chosen rows of `h`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L931-L937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L931-L937

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

theorem QEC.Coding.ProductExpansion.card_productKernel_fixed_word_mul_field_pow_rank_eq_total
    (h' : Matrix R' W F) (x : Matrix W W F) :
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ ((h' * x).rank * Fintype.card R) =
      Nat.card (Matrix R W F) := by sorry
