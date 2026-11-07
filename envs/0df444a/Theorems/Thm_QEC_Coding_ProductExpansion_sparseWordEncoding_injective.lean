-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_sparseWordEncoding_injective
-- name    : QEC.Coding.ProductExpansion.sparseWordEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:25.239303+00:00
-- url     : https://prove2.me/theorems/76b39caa-6548-4989-9f7a-7eec729b07bb
-- title:
--   Product Expansion: sparse Word Encoding injective
-- statement:
--   The sparse-word encoding is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L232-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L232-L251

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

theorem QEC.Coding.ProductExpansion.sparseWordEncoding_injective
    [DecidableEq W] (d : Nat) :
    Function.Injective (sparseWordEncoding (F := F) (W := W) d) := by sorry
