-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_left_mul_ne_zero_of_nonzero_minimal
-- name    : QEC.Coding.ProductExpansion.left_mul_ne_zero_of_nonzero_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:48.861422+00:00
-- url     : https://prove2.me/theorems/2406ad24-31f3-4e3e-9c69-df4bfc786c89
-- title:
--   Product Expansion: left mul ne zero of nonzero minimal
-- statement:
--   The left syndrome of a nonzero minimal matrix must be nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L508-L518
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L508-L518

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

theorem QEC.Coding.ProductExpansion.left_mul_ne_zero_of_nonzero_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    h' * x ≠ 0 := by sorry
