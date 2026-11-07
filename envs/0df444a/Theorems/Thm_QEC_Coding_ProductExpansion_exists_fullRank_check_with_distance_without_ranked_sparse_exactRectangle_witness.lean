-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
-- name    : QEC.Coding.ProductExpansion.exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:51.086321+00:00
-- url     : https://prove2.me/theorems/a09e1e64-a667-42a4-8eb6-115695563568
-- title:
--   Product Expansion: exists full Rank check with distance without ranked sparse exact Rectangle witness
-- statement:
--   Simultaneous random-check existence with the full-rank condition needed
--   by the local-star syndrome lift. The selected matrix has both kernel distance
--   and transpose-image distance at least d, hence maximal row rank for d > 0,
--   and excludes every ranked sparse exact-rectangle witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1417-L1578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1417-L1578

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
omit [Fintype R']
set_option maxHeartbeats 800000

theorem QEC.Coding.ProductExpansion.exists_fullRank_check_with_distance_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
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
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 →
        d ≤ HammingWeight c) ∧
      (∀ a : Word F R, a ≠ 0 →
        d ≤ HammingWeight (h.transpose.mulVec a)) ∧
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by sorry
