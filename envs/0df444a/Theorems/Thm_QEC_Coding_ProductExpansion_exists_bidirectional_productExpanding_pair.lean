-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_bidirectional_productExpanding_pair
-- name    : QEC.Coding.ProductExpansion.exists_bidirectional_productExpanding_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:09.868129+00:00
-- url     : https://prove2.me/theorems/8e2f693e-d015-475e-814a-a3b7609ba708
-- title:
--   Product Expansion: exists bidirectional product Expanding pair
-- statement:
--   The simultaneous random-local-code package used by PK22. One pair
--   `(h,g')` has maximal row rank, distance at least `d` for both kernels and
--   both row images, and product expansion in the two orientations required by
--   the lifted-product argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L930-L1009
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L930-L1009

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

theorem QEC.Coding.ProductExpansion.exists_bidirectional_productExpanding_pair
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
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
      h.rank = Fintype.card R ∧
      g'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck h)).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode g').carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpanding g' (generatorImageParityCheck h) s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
