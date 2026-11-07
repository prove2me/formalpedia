-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badSecondImagePairs_mul_penalty_le
-- name    : QEC.Coding.ProductExpansion.card_badSecondImagePairs_mul_penalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:25.153752+00:00
-- url     : https://prove2.me/theorems/c960b763-f852-4d91-95a9-2e57f8d3016e
-- title:
--   Product Expansion: card bad Second Image Pairs mul penalty le
-- statement:
--   The second row-image bad-pair count has the symmetric ambient-length
--   penalty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L459-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L459-L491

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

theorem QEC.Coding.ProductExpansion.card_badSecondImagePairs_mul_penalty_le (d : Nat) :
    Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by sorry
