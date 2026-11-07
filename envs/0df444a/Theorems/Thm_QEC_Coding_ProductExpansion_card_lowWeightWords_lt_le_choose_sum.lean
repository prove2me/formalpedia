-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_lowWeightWords_lt_le_choose_sum
-- name    : QEC.Coding.ProductExpansion.card_lowWeightWords_lt_le_choose_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:48.894631+00:00
-- url     : https://prove2.me/theorems/69ff6c12-16f4-4f1d-9485-079cb867e377
-- title:
--   Product Expansion: card low Weight Words lt le choose sum
-- statement:
--   Exact binomial support-count upper bound for low-weight words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L254-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L254-L287

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

theorem QEC.Coding.ProductExpansion.card_lowWeightWords_lt_le_choose_sum
    [DecidableEq W] (d : Nat) :
    Nat.card {c : Word F W // HammingWeight c < d} ≤
      ∑ t : Fin d, Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1 := by sorry
