-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_eq_field_pow_nullity
-- name    : QEC.Coding.ProductExpansion.card_leftProductKernel_eq_field_pow_nullity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:33.09681+00:00
-- url     : https://prove2.me/theorems/b751daf8-f631-4612-96bc-04ba0b8a0b3b
-- title:
--   Product Expansion: card left Product Kernel eq field pow nullity
-- statement:
--   Rank-nullity makes the exact constraint count a power of the field size.
--   For a uniform random `h`, comparison with the total number of matrices will
--   give one factor of `|F|^{-rank M}` for each row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L440-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L440-L454

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

theorem QEC.Coding.ProductExpansion.card_leftProductKernel_eq_field_pow_nullity
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card F) ^ ((Fintype.card W - M.rank) * Fintype.card R) := by sorry
