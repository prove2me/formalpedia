-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForDistance_mul_field_pow_rows_le
-- name    : QEC.Coding.ProductExpansion.card_badChecksForDistance_mul_field_pow_rows_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:43.25472+00:00
-- url     : https://prove2.me/theorems/a51e8e95-3675-46f6-8efa-0f951781a662
-- title:
--   Product Expansion: card bad Checks For Distance mul field pow rows le
-- statement:
--   Gilbert--Varshamov finite union bound: distance-bad checks pay one field
--   factor for each independently selected row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L532-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L532-L573

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

theorem QEC.Coding.ProductExpansion.card_badChecksForDistance_mul_field_pow_rows_le
    [DecidableEq W] (d : Nat) :
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R ≤
      Nat.card {c : Word F W // HammingWeight c < d} *
        Nat.card (Matrix R W F) := by sorry
