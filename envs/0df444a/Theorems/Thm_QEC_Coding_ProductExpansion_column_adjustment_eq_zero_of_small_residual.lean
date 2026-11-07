-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_adjustment_eq_zero_of_small_residual
-- name    : QEC.Coding.ProductExpansion.column_adjustment_eq_zero_of_small_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:41.84027+00:00
-- url     : https://prove2.me/theorems/b9591d1e-791a-4e6c-ae11-5612325814fd
-- title:
--   Product Expansion: column adjustment eq zero of small residual
-- statement:
--   A `d/3`-minimal column cannot differ by a nonzero local codeword from a
--   word of weight strictly less than `d/3`. This is the cancellation argument
--   used twice in the source's rank lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L422-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L422-L443

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

theorem QEC.Coding.ProductExpansion.column_adjustment_eq_zero_of_small_residual
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (j : W) (c : Word F W) (hc : c ∈ (parityCheckCode h').carrier)
    (hSmall : (HammingWeight (column x j + c) : ℝ) < (d : ℝ) / 3) :
    c = 0 := by sorry
