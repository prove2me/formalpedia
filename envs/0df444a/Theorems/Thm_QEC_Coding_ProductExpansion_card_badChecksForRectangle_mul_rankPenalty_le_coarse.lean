-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForRectangle_mul_rankPenalty_le_coarse
-- name    : QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:18.013625+00:00
-- url     : https://prove2.me/theorems/196242f8-e0ba-4972-8350-8cd953b58326
-- title:
--   Product Expansion: card bad Checks For Rectangle mul rank Penalty le coarse
-- statement:
--   One-rectangle PK22 union bound after inserting the coarse sparse-matrix
--   count and the certified syndrome-rank penalty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1045-L1059
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1045-L1059

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

theorem QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le_coarse
    [DecidableEq W]
    (h' : Matrix R' W F) (A B : Finset W) (s k m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
          Nat.card (Matrix R W F) := by sorry
