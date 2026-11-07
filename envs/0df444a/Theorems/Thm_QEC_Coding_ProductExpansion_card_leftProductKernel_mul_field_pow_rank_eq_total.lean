-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_leftProductKernel_mul_field_pow_rank_eq_total
-- name    : QEC.Coding.ProductExpansion.card_leftProductKernel_mul_field_pow_rank_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:56.149962+00:00
-- url     : https://prove2.me/theorems/18cfff9e-9cc2-4b7f-a6f1-3c129816c444
-- title:
--   Product Expansion: card left Product Kernel mul field pow rank eq total
-- statement:
--   The exact count of good check matrices times the rank penalty equals
--   the total number of check matrices. This avoids division by finite
--   cardinalities until a probability bound actually needs it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L460-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L460-L481

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

theorem QEC.Coding.ProductExpansion.card_leftProductKernel_mul_field_pow_rank_eq_total
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} *
        (Nat.card F) ^ (M.rank * Fintype.card R) =
      Nat.card (Matrix R W F) := by sorry
