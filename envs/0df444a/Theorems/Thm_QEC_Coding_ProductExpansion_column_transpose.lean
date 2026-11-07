-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
-- name    : QEC.Coding.ProductExpansion.column_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:24:34.441731+00:00
-- url     : https://prove2.me/theorems/558ec973-3bde-495e-bc74-1a7d95e9eac1
-- title:
--   Product Expansion: column transpose
-- statement:
--   The Product Expansion construction uses the column transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L407-L408
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L407-L408

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype W]

theorem QEC.Coding.ProductExpansion.column_transpose (x : Matrix W W F) (j : W) :
    column x.transpose j = row x j := by sorry

attribute [defeq] QEC.Coding.ProductExpansion.column_transpose
