-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_rightProduct_mem_parityCheckCode
-- name    : QEC.Coding.ProductExpansion.column_rightProduct_mem_parityCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:55:23.8702+00:00
-- url     : https://prove2.me/theorems/58b6d4f3-2f15-425c-936f-d863808eed8f
-- title:
--   Product Expansion: column right Product mem parity Check Code
-- statement:
--   Each column of the second local syndrome is a codeword of the first check code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L54-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L54-L66

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
omit [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.column_rightProduct_mem_parityCheckCode
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x) (j : R) :
    (fun i : W => (x * h.transpose) i j) ∈ (parityCheckCode h').carrier := by sorry
