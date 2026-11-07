-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_sparseRectangleEncoding_injective
-- name    : QEC.Coding.ProductExpansion.sparseRectangleEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:50.425366+00:00
-- url     : https://prove2.me/theorems/02e05aa2-84e5-4d0b-bec1-e40a020f3c33
-- title:
--   Product Expansion: sparse Rectangle Encoding injective
-- statement:
--   The sparse rectangle encoding loses no matrix information.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L65-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L65-L93

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
omit [Fintype F]

theorem QEC.Coding.ProductExpansion.sparseRectangleEncoding_injective
    [DecidableEq W]
    (A B : Finset W) (s : Nat) :
    Function.Injective (sparseRectangleEncoding (F := F) A B s) := by sorry
