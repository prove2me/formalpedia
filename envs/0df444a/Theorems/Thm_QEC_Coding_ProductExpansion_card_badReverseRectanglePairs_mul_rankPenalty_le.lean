-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badReverseRectanglePairs_mul_rankPenalty_le
-- name    : QEC.Coding.ProductExpansion.card_badReverseRectanglePairs_mul_rankPenalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:12.815889+00:00
-- url     : https://prove2.me/theorems/1bcdad0e-f015-456b-a941-1132aa68266c
-- title:
--   Product Expansion: card bad Reverse Rectangle Pairs mul rank Penalty le
-- statement:
--   Uniform sparse-rectangle count in the reverse orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L324-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L324-L353

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
include hRFinite

theorem QEC.Coding.ProductExpansion.card_badReverseRectanglePairs_mul_rankPenalty_le
    (s m k : Nat) :
    Nat.card (badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) *
        (Nat.card F) ^ (k * Fintype.card R') ≤
      ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) *
        Nat.card (LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by sorry
