-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForRectangle_mul_rankPenalty_le
-- name    : QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:14.59727+00:00
-- url     : https://prove2.me/theorems/6098561f-349f-4382-a9c7-950795a04a75
-- title:
--   Product Expansion: card bad Checks For Rectangle mul rank Penalty le
-- statement:
--   Finite union bound for one rectangle: the number of bad check matrices,
--   times the rank penalty, is at most the number of sparse candidate matrices
--   times the total number of check matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1001-L1040
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1001-L1040

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

theorem QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card {x : Matrix W W F // restrictedWeight x A B < s} *
        Nat.card (Matrix R W F) := by sorry
