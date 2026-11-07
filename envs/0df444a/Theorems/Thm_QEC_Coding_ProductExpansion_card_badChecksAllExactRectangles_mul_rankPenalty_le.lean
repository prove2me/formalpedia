-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksAllExactRectangles_mul_rankPenalty_le
-- name    : QEC.Coding.ProductExpansion.card_badChecksAllExactRectangles_mul_rankPenalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:52.809959+00:00
-- url     : https://prove2.me/theorems/7db99a6a-98c9-42c8-b198-670725de83af
-- title:
--   Product Expansion: card bad Checks All Exact Rectangles mul rank Penalty le
-- statement:
--   Full finite PK22 union bound over all exact large rectangles. The squared
--   binomial coefficient is the exact number of choices for `A` and `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1187-L1242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1187-L1242

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

theorem QEC.Coding.ProductExpansion.card_badChecksAllExactRectangles_mul_rankPenalty_le
    [DecidableEq W]
    (h' : Matrix R' W F) (s m k : Nat) :
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
        Nat.card (Matrix R W F) := by sorry
