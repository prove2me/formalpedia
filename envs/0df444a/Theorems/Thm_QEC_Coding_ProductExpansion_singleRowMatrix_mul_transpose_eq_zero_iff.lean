-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_singleRowMatrix_mul_transpose_eq_zero_iff
-- name    : QEC.Coding.ProductExpansion.singleRowMatrix_mul_transpose_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:33.249321+00:00
-- url     : https://prove2.me/theorems/d57fba63-3900-42fe-9111-abdcb1a681b9
-- title:
--   Product Expansion: single Row Matrix mul transpose eq zero iff
-- statement:
--   The one-row left-product equation says that every row of `h` is
--   orthogonal to the fixed word `c`, equivalently `h.mulVec c = 0`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L303-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L303-L317

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.singleRowMatrix_mul_transpose_eq_zero_iff
    (h : Matrix R W F) (c : Word F W) :
    singleRowMatrix c * h.transpose = 0 ↔ h.mulVec c = 0 := by sorry
