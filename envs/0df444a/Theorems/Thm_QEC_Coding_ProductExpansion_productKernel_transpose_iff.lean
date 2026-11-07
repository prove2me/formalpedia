-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_productKernel_transpose_iff
-- name    : QEC.Coding.ProductExpansion.productKernel_transpose_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:24:32.949198+00:00
-- url     : https://prove2.me/theorems/5672c84b-fa61-495f-86c4-30c439871c78
-- title:
--   Product Expansion: product Kernel transpose iff
-- statement:
--   Transposition exchanges the two product-kernel parity checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L656-L668
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L656-L668

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.productKernel_transpose_iff
    (h : Matrix R W F) (h' : Matrix R' W F) (x : Matrix W W F) :
    ProductKernel h h' x ↔ ProductKernel h' h x.transpose := by sorry
