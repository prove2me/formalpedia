-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
-- name    : QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:58.980775+00:00
-- url     : https://prove2.me/theorems/c7f48d48-0dba-43d8-a820-f4684c76e3ec
-- title:
--   Product Expansion: card bad Generators For Distance mul field pow length le choose sum
-- statement:
--   Random-generator GV bound with the low-weight output count expanded as a
--   finite binomial support sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L753-L766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L753-L766

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

theorem QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
    [DecidableEq W] (d : Nat) :
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (Matrix R W F) := by sorry
