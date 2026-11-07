-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_badChecksAllExactRectangles_of_local_failure
-- name    : QEC.Coding.ProductExpansion.exists_badChecksAllExactRectangles_of_local_failure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:27.824415+00:00
-- url     : https://prove2.me/theorems/c1949cd4-57f6-42ff-8946-3cc0f2ebf66f
-- title:
--   Product Expansion: exists bad Checks All Exact Rectangles of local failure
-- statement:
--   Any low-weight local-minimal product-kernel witness yields an exact
--   rectangle witness with the integer syndrome-rank threshold supplied by the
--   PK22 local rank lemma.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1141-L1182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1141-L1182

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
omit [Fintype R]

theorem QEC.Coding.ProductExpansion.exists_badChecksAllExactRectangles_of_local_failure
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card)
    (hWeight : restrictedWeight x A B < s) :
    ∃ bad : badChecksAllExactRectangles (R := R) h' s m k, bad.1 = h := by sorry
