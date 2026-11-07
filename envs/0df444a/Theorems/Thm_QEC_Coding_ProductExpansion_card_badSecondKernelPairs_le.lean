-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badSecondKernelPairs_le
-- name    : QEC.Coding.ProductExpansion.card_badSecondKernelPairs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:12.841785+00:00
-- url     : https://prove2.me/theorems/af5b650a-d773-4355-b651-64bb3be6cc27
-- title:
--   Product Expansion: card bad Second Kernel Pairs le
-- statement:
--   Cardinal bound for second-kernel-bad pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L224-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L224-L240

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

theorem QEC.Coding.ProductExpansion.card_badSecondKernelPairs_le (d : Nat) :
    Nat.card (badSecondKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badChecksForDistance (F := F) (W := W) (R := R') d) := by sorry
