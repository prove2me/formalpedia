-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_fullRank_generator_check_productExpanding_pair
-- name    : QEC.Coding.ProductExpansion.exists_fullRank_generator_check_productExpanding_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:03:19.784421+00:00
-- url     : https://prove2.me/theorems/ef9cbdb7-0fb5-4f8f-a2b7-fce6e3715135
-- title:
--   Product Expansion: exists full Rank generator check product Expanding pair
-- statement:
--   Source-aligned random local pair with maximal row rank on both the
--   generator matrix g' and the first parity check h. This is the exact local
--   package required by the concrete PK22 active-vertex theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1943-L1990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1943-L1990

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
set_option maxHeartbeats 800000

theorem QEC.Coding.ProductExpansion.exists_fullRank_generator_check_productExpanding_pair
    [DecidableEq W]
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hGeneratorFactor :
      (Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W)
    (hCheckDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hCheckImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ (g' : Matrix R' W F) (h : Matrix R W F),
      g'.rank = Fintype.card R' ∧
      h.rank = Fintype.card R ∧
      (∀ c : Word F W,
        c ∈ (parityCheckCode (generatorImageParityCheck g')).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h (generatorImageParityCheck g') s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
