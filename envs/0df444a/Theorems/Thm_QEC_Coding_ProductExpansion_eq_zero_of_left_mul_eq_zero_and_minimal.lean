-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_left_mul_eq_zero_and_minimal
-- name    : QEC.Coding.ProductExpansion.eq_zero_of_left_mul_eq_zero_and_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:54.26925+00:00
-- url     : https://prove2.me/theorems/cd4e4834-568e-426e-ad22-da29089e6919
-- title:
--   Product Expansion: eq zero of left mul eq zero and minimal
-- statement:
--   If the left syndrome vanishes, local minimality below the local distance
--   forces every column, hence the whole matrix, to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L482-L504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L482-L504

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

theorem QEC.Coding.ProductExpansion.eq_zero_of_left_mul_eq_zero_and_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hLeft : h' * x = 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    x = 0 := by sorry
