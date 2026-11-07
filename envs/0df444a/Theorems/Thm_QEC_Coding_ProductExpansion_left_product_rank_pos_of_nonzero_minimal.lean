-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_left_product_rank_pos_of_nonzero_minimal
-- name    : QEC.Coding.ProductExpansion.left_product_rank_pos_of_nonzero_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:42.248327+00:00
-- url     : https://prove2.me/theorems/d1f5bcff-8c95-4756-8f53-5a557057b2a3
-- title:
--   Product Expansion: left product rank pos of nonzero minimal
-- statement:
--   The source's syndrome rank parameter is positive for every nonzero
--   locally minimal matrix, before its quantitative lower bound is established.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L541-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L541-L551

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

theorem QEC.Coding.ProductExpansion.left_product_rank_pos_of_nonzero_minimal
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    0 < (h' * x).rank := by sorry
