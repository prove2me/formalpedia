-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_productExpanding_swap
-- name    : QEC.Coding.ProductExpansion.productExpanding_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:00:50.251787+00:00
-- url     : https://prove2.me/theorems/6a7fbdb4-121f-4c71-8cef-4fac782d4499
-- title:
--   Product Expansion: product Expanding swap
-- statement:
--   Product expansion is symmetric under exchanging the two parity checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L2059-L2089
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L2059-L2089

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

theorem QEC.Coding.ProductExpansion.productExpanding_swap
    (h : Matrix R W F) (h' : Matrix R' W F)
    (s m : Nat) (beta : ℝ) :
    ProductExpanding h h' s m beta ↔ ProductExpanding h' h s m beta := by sorry
