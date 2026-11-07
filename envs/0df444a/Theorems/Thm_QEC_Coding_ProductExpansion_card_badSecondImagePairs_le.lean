-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badSecondImagePairs_le
-- name    : QEC.Coding.ProductExpansion.card_badSecondImagePairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:01.676075+00:00
-- url     : https://prove2.me/theorems/4d896f5e-eea8-4014-aa9e-a0015b37e5f7
-- title:
--   Product Expansion: card bad Second Image Pairs le
-- statement:
--   Cardinal bound for second-image-bad pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L244-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L244-L260

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [DecidableEq W]

theorem QEC.Coding.ProductExpansion.card_badSecondImagePairs_le (d : Nat) :
    Nat.card (badSecondImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R') d) := by sorry
