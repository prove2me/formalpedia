-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_mem_generatorImage_iff
-- name    : QEC.Coding.ProductExpansion.mem_generatorImage_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:01:58.086468+00:00
-- url     : https://prove2.me/theorems/e4aa2b3f-27c1-4003-b296-50793741d83c
-- title:
--   Product Expansion: mem generator Image iff
-- statement:
--   Membership in the row-generated image has an instance-independent
--   matrix-vector witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L830-L840
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L830-L840

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
omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R']

theorem QEC.Coding.ProductExpansion.mem_generatorImage_iff
    (g : Matrix R W F) (c : Word F W) :
    c ∈ generatorImage g ↔
      ∃ a : Word F R, g.transpose.mulVec a = c := by sorry
