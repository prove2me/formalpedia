-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_zero_rectangle_one_third_either
-- name    : QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle_one_third_either
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:58.524204+00:00
-- url     : https://prove2.me/theorems/26bddec9-4041-44fd-b623-ccf4899304c1
-- title:
--   Product Expansion: eq zero of zero rectangle one third either
-- statement:
--   The source's nonzero-block lemma in both rectangle orientations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L755-L786
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L755-L786

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

theorem QEC.Coding.ProductExpansion.eq_zero_of_zero_rectangle_one_third_either
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A B : Finset W)
    (hSizeA : (Fintype.card W : ℝ) - A.card < (d : ℝ) / 3)
    (hSizeB : Fintype.card W - d < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (hRectangle : (∀ i ∈ B, ∀ j ∈ A, x i j = 0) ∨
      (∀ i ∈ A, ∀ j ∈ B, x i j = 0)) :
    x = 0 := by sorry
