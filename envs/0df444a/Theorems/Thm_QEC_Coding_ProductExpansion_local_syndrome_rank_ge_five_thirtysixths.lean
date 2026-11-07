-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_local_syndrome_rank_ge_five_thirtysixths
-- name    : QEC.Coding.ProductExpansion.local_syndrome_rank_ge_five_thirtysixths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:59:29.341891+00:00
-- url     : https://prove2.me/theorems/07e1fbca-58ea-4fce-ad3f-38170e299e08
-- title:
--   Product Expansion: local syndrome rank ge five thirtysixths
-- statement:
--   The source's local rank estimate in its real-valued `5d²/(36s)` form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1940-L1968
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1940-L1968

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

theorem QEC.Coding.ProductExpansion.local_syndrome_rank_ge_five_thirtysixths
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat) (s : ℝ)
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
    (hLargeB : Fintype.card W - m ≤ B.card)
    (hSmallWeight : (restrictedWeight x A B : ℝ) < s)
    (hs : 0 < s) :
    (5 : ℝ) / 36 * (d : ℝ) ^ 2 / s ≤ ((h' * x).rank : ℝ) := by sorry
