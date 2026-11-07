-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badBidirectionalLocalPairs_le_add
-- name    : QEC.Coding.ProductExpansion.card_badBidirectionalLocalPairs_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:23.161378+00:00
-- url     : https://prove2.me/theorems/e259e3ad-dee0-4c77-9380-8fd906731082
-- title:
--   Product Expansion: card bad Bidirectional Local Pairs le add
-- statement:
--   Six-event finite union bound for a uniformly chosen ordered pair of
--   local matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L623-L664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L623-L664

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

theorem QEC.Coding.ProductExpansion.card_badBidirectionalLocalPairs_le_add
    (d s m k : Nat) :
    Nat.card (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) ≤
      Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) +
      Nat.card (badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) := by sorry
