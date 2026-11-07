-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badForwardRectanglePairs_mul_rankPenalty_le
-- name    : QEC.Coding.ProductExpansion.card_badForwardRectanglePairs_mul_rankPenalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:18.42513+00:00
-- url     : https://prove2.me/theorems/573f53cc-66fc-4988-923e-345525957066
-- title:
--   Product Expansion: card bad Forward Rectangle Pairs mul rank Penalty le
-- statement:
--   Uniform sparse-rectangle count in the forward orientation, summed over
--   all choices of the second matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L291-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L291-L320

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
include hR'Finite

theorem QEC.Coding.ProductExpansion.card_badForwardRectanglePairs_mul_rankPenalty_le
    (s m k : Nat) :
    Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) *
        Nat.card (LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by sorry
