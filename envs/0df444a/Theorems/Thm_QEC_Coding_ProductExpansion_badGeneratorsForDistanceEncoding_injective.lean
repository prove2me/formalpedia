-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badGeneratorsForDistanceEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badGeneratorsForDistanceEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:55.559974+00:00
-- url     : https://prove2.me/theorems/5eb002bb-5c04-46b6-a7fd-26177fbc5ac0
-- title:
--   Product Expansion: bad Generators For Distance Encoding injective
-- statement:
--   The generator-distance witness encoding retains the generator matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L689-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L689-L694

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
omit [Fintype F] [Fintype R']

theorem QEC.Coding.ProductExpansion.badGeneratorsForDistanceEncoding_injective (d : Nat) :
    Function.Injective
      (badGeneratorsForDistanceEncoding (F := F) (W := W) (R := R) d) := by sorry
