-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badGeneratorsForDistance_mul_field_pow_length_le
-- name    : QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:53.198088+00:00
-- url     : https://prove2.me/theorems/7bed7bdf-d446-4001-b792-01d84d95c100
-- title:
--   Product Expansion: card bad Generators For Distance mul field pow length le
-- statement:
--   Finite union bound for random generator codes. The penalty has one field
--   factor per output coordinate, while the witness count has one factor per
--   message and one low-weight target word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L700-L748
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L700-L748

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
omit [Fintype R']

theorem QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le
    [DecidableEq W] (d : Nat) :
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W ≤
      (Nat.card F) ^ Fintype.card R *
        Nat.card {y : Word F W // HammingWeight y < d} *
        Nat.card (Matrix R W F) := by sorry
