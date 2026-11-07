-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_row_correction_of_zero_rectangle
-- name    : QEC.Coding.ProductExpansion.exists_row_correction_of_zero_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:30.384977+00:00
-- url     : https://prove2.me/theorems/b391b47a-ce65-4a41-a121-52358634fe88
-- title:
--   Product Expansion: exists row correction of zero rectangle
-- statement:
--   The algebraic correction step of the nonzero-block argument. The selected
--   rectangle is zero, and each local code is determined by its corresponding
--   selected coordinate set. The correction has local-code rows; after subtracting
--   it, the second syndrome and all columns in `A` vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L378-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L378-L400

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

theorem QEC.Coding.ProductExpansion.exists_row_correction_of_zero_rectangle
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W) (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∃ delta : Matrix W W F,
      h' * (x - delta) = 0 ∧
      (∀ j ∈ A, column (x - delta) j = 0) ∧
      (∀ i : W, row delta i ∈ (parityCheckCode h).carrier) := by sorry
