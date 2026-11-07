-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle_transpose
-- name    : QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:57:01.925644+00:00
-- url     : https://prove2.me/theorems/68507798-f193-4283-87c9-70f61b48cee3
-- title:
--   Product Expansion: eq zero of zero rectangle transpose
-- statement:
--   Nonzero-block lemma in the opposite rectangle orientation, obtained by
--   transposing the matrix and exchanging the two local codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L690-L719
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L690-L719

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle_transpose
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W)
    (hLargeA : Fintype.card W - d' < A.card)
    (hLargeB : Fintype.card W - d < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d')
    (hDelta : delta < d)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ A, ∀ j ∈ B, x i j = 0) :
    x = 0 := by sorry
