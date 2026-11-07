-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_transpose
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:30:59.974976+00:00
-- url     : https://prove2.me/theorems/e81ab271-c931-444b-ac18-d3aa3309d36c
-- title:
--   Product Expansion: restricted Weight transpose
-- statement:
--   Transposition exchanges the two axes of a restricted rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L672-L676
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L672-L676

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
omit [Fintype F] [Fintype W]

theorem QEC.Coding.ProductExpansion.restrictedWeight_transpose (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x.transpose A B = restrictedWeight x B A := by sorry
