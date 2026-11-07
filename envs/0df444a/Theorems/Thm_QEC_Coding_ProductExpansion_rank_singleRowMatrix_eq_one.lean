-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_rank_singleRowMatrix_eq_one
-- name    : QEC.Coding.ProductExpansion.rank_singleRowMatrix_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:04.801035+00:00
-- url     : https://prove2.me/theorems/4799af14-408f-4067-8f9a-c3f1ef6a62c5
-- title:
--   Product Expansion: rank single Row Matrix eq one
-- statement:
--   A nonzero one-row matrix has rank one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L294-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L294-L298

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

theorem QEC.Coding.ProductExpansion.rank_singleRowMatrix_eq_one
    (c : Word F W) (hc : c ≠ 0) : (singleRowMatrix c).rank = 1 := by sorry
