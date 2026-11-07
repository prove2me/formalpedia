-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
-- name    : QEC.Coding.ProductExpansion.exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:42.978137+00:00
-- url     : https://prove2.me/theorems/261fbab0-3abb-40e7-a3fa-6a9a4dd32bd7
-- title:
--   Product Expansion: exists check with distance without ranked sparse exact Rectangle witness
-- statement:
--   Simultaneous finite-field existence: if both union factors are below
--   half of their respective penalties, one check matrix has classical distance
--   at least `d` and has no ranked sparse witness on any exact large rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1585-L1698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1585-L1698

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

theorem QEC.Coding.ProductExpansion.exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 → d ≤ HammingWeight c) ∧
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by sorry
