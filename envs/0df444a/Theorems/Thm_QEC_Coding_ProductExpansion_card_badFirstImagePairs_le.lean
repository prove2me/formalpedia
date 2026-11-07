-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstImagePairs_le
-- name    : QEC.Coding.ProductExpansion.card_badFirstImagePairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:52.767444+00:00
-- url     : https://prove2.me/theorems/eb18454c-5cae-4670-86ac-6273d7cb66fd
-- title:
--   Product Expansion: card bad First Image Pairs le
-- statement:
--   Cardinal bound for first-image-bad pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L204-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L204-L220

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

theorem QEC.Coding.ProductExpansion.card_badFirstImagePairs_le (d : Nat) :
    Nat.card (badFirstImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by sorry
