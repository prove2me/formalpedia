-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_row_leftProduct_mem_parityCheckCode
-- name    : QEC.Coding.ProductExpansion.row_leftProduct_mem_parityCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:23.132763+00:00
-- url     : https://prove2.me/theorems/b682a494-6136-4978-9906-a3fbb9142c67
-- title:
--   Product Expansion: row left Product mem parity Check Code
-- statement:
--   Each row of the first local syndrome is a codeword of the other check code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L40-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L40-L50

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

theorem QEC.Coding.ProductExpansion.row_leftProduct_mem_parityCheckCode
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) (hx : ProductKernel h h' x) (i : R') :
    (h' * x) i ∈ (parityCheckCode h).carrier := by sorry
