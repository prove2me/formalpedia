-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_distance_and_productExpanding_check
-- name    : QEC.Coding.ProductExpansion.exists_distance_and_productExpanding_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:52.591166+00:00
-- url     : https://prove2.me/theorems/5f91e595-c05a-4525-93ce-28175aa191f3
-- title:
--   Product Expansion: exists distance and product Expanding check
-- statement:
--   Complete finite random-local step of the PK22 argument. Under the two
--   explicit finite union inequalities and the deterministic integer parameter
--   conditions, one check matrix simultaneously has classical distance `d` and
--   forms a product-expanding pair with the fixed check matrix `h'`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1817-L1846
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1817-L1846

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

theorem QEC.Coding.ProductExpansion.exists_distance_and_productExpanding_check
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
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
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
        c ≠ 0 → d ≤ HammingWeight c) ∧
      ProductExpanding h h' s m
        ((d : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
