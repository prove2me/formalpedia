-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstKernelPairs_le
-- name    : QEC.Coding.ProductExpansion.card_badFirstKernelPairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:36.536198+00:00
-- url     : https://prove2.me/theorems/52c2e5b4-a86e-4328-89f5-a1553b46eab2
-- title:
--   Product Expansion: card bad First Kernel Pairs le
-- statement:
--   Cardinal bound for first-kernel-bad pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L184-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L184-L200

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

theorem QEC.Coding.ProductExpansion.card_badFirstKernelPairs_le (d : Nat) :
    Nat.card (badFirstKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by sorry
