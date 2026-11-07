-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_local_syndrome_rank_weight_inequality
-- name    : QEC.Coding.ProductExpansion.local_syndrome_rank_weight_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:37.264244+00:00
-- url     : https://prove2.me/theorems/b78bc9a0-1d70-44ed-92ca-d8a19cfb4123
-- title:
--   Product Expansion: local syndrome rank weight inequality
-- statement:
--   The integer counting form of the source's local rank lemma. This has no
--   division and remains valid even when the rectangle weight is zero (which the
--   inequality then excludes for positive distance).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1880-L1910
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1880-L1910

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]

theorem QEC.Coding.ProductExpansion.local_syndrome_rank_weight_inequality
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card) :
    d * (d - m) ≤ 6 * (h' * x).rank * restrictedWeight x A B := by sorry
