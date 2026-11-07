-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_mem_parityCheckCode_of_left_mul_eq_zero
-- name    : QEC.Coding.ProductExpansion.column_mem_parityCheckCode_of_left_mul_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:24:58.256612+00:00
-- url     : https://prove2.me/theorems/11a53bd6-a90d-4f54-b68a-f550503d9b39
-- title:
--   Product Expansion: column mem parity Check Code of left mul eq zero
-- statement:
--   A vanishing left syndrome means that every column belongs to the local code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L231-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L231-L239

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
omit [DecidableEq F] [Fintype R]

theorem QEC.Coding.ProductExpansion.column_mem_parityCheckCode_of_left_mul_eq_zero
    (h : Matrix R W F) (x : Matrix W W F) (hx : h * x = 0) (j : W) :
    column x j ∈ (parityCheckCode h).carrier := by sorry
