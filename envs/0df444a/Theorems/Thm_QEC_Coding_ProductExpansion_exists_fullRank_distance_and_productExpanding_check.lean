-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_fullRank_distance_and_productExpanding_check
-- name    : QEC.Coding.ProductExpansion.exists_fullRank_distance_and_productExpanding_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:50.933456+00:00
-- url     : https://prove2.me/theorems/03340813-57d2-445e-9c99-342bd8c5f3fa
-- title:
--   Product Expansion: exists full Rank distance and product Expanding check
-- statement:
--   Random first-check construction with the additional maximal-row-rank
--   certificate consumed by the concrete Tanner-star syndrome lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1899-L1937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1899-L1937

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

theorem QEC.Coding.ProductExpansion.exists_fullRank_distance_and_productExpanding_check
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistanceFactor :
      3 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hImageFactor :
      3 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hRectangleFactor :
      3 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      h.rank = Fintype.card R ∧
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
