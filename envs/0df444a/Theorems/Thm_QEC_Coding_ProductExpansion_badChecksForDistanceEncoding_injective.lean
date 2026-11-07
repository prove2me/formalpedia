-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksForDistanceEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badChecksForDistanceEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:44.130914+00:00
-- url     : https://prove2.me/theorems/db472dd2-bb0c-4daa-92da-86ce46f15250
-- title:
--   Product Expansion: bad Checks For Distance Encoding injective
-- statement:
--   Choosing a low-weight kernel witness retains the check matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L522-L527
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L522-L527

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
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.badChecksForDistanceEncoding_injective (d : Nat) :
    Function.Injective
      (badChecksForDistanceEncoding (F := F) (W := W) (R := R) d) := by sorry
