-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
-- name    : QEC.Coding.ProductExpansion.card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:52.089414+00:00
-- url     : https://prove2.me/theorems/1c5923b1-91a9-4f18-9009-73986c552c8a
-- title:
--   Product Expansion: card checks annihilating nonzero word mul field pow rows eq total
-- statement:
--   Exact count of check matrices annihilating one fixed nonzero word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L485-L496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L485-L496

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

theorem QEC.Coding.ProductExpansion.card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
    (c : Word F W) (hc : c ≠ 0) :
    Nat.card {h : Matrix R W F // h.mulVec c = 0} *
        (Nat.card F) ^ Fintype.card R = Nat.card (Matrix R W F) := by sorry
