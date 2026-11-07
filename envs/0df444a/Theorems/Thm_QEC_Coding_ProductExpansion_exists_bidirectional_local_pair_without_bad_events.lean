-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_bidirectional_local_pair_without_bad_events
-- name    : QEC.Coding.ProductExpansion.exists_bidirectional_local_pair_without_bad_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:41.521059+00:00
-- url     : https://prove2.me/theorems/8b892f5e-6ae3-4001-bc12-4390f6008a30
-- title:
--   Product Expansion: exists bidirectional local pair without bad events
-- statement:
--   A finite six-event union bound chooses one ordered matrix pair that
--   simultaneously has kernel and row-image distance in both components and has
--   no ranked sparse rectangle witness in either product orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L686-L923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L686-L923

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
set_option maxHeartbeats 1200000

theorem QEC.Coding.ProductExpansion.exists_bidirectional_local_pair_without_bad_events
    (d s m k : Nat)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R')) :
    ∃ (h : Matrix R W F) (g' : Matrix R' W F),
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R, a ≠ 0 →
        d ≤ HammingWeight (h.transpose.mulVec a)) ∧
      (∀ c : Word F W, g'.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R', a ≠ 0 →
        d ≤ HammingWeight (g'.transpose.mulVec a)) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck g' * x).rank ∧
          ProductKernel h (generatorImageParityCheck g') x) ∧
      (¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (generatorImageParityCheck h * x).rank ∧
          ProductKernel g' (generatorImageParityCheck h) x) := by sorry
