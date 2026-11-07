-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstKernelPairs_mul_penalty_le
-- name    : QEC.Coding.ProductExpansion.card_badFirstKernelPairs_mul_penalty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:12.176759+00:00
-- url     : https://prove2.me/theorems/8bda028e-61a2-45df-99c6-6ae7de2a958e
-- title:
--   Product Expansion: card bad First Kernel Pairs mul penalty le
-- statement:
--   The first-kernel bad-pair count inherits the usual low-word factor and
--   the first matrix's row-syndrome penalty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L357-L386
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L357-L386

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

theorem QEC.Coding.ProductExpansion.card_badFirstKernelPairs_mul_penalty_le (d : Nat) :
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R ≤
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by sorry
