-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle
-- name    : QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:40.252297+00:00
-- url     : https://prove2.me/theorems/4afc858c-dab7-47a5-875a-3438dd7269da
-- title:
--   Product Expansion: eq zero of zero rectangle
-- statement:
--   Nonzero-block lemma, in the orientation where `A` selects columns and
--   `B` selects rows. The exact numerical inequalities are exposed so that the
--   source's `d/3` parameter choice can be instantiated separately.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L583-L608
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L583-L608

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

theorem QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W)
    (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (hDelta : delta < d')
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' delta x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    x = 0 := by sorry
