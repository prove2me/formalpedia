-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_eq_sum_column_restrictedHammingWeight
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_eq_sum_column_restrictedHammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:02.702767+00:00
-- url     : https://prove2.me/theorems/bf07b2b7-234a-4927-a981-48c6d995eeef
-- title:
--   Product Expansion: restricted Weight eq sum column restricted Hamming Weight
-- statement:
--   Count the nonzero entries of a rectangle by columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1121-L1127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1121-L1127

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
omit [Fintype F] [Fintype W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.restrictedWeight_eq_sum_column_restrictedHammingWeight
    (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x A B =
      ∑ j ∈ B, restrictedHammingWeight A (column x j) := by sorry
