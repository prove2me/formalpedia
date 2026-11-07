-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceOrRectanglesEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badChecksDistanceOrRectanglesEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:36.010541+00:00
-- url     : https://prove2.me/theorems/784ec11a-a7ae-4fb2-9744-87ea0938d7db
-- title:
--   Product Expansion: bad Checks Distance Or Rectangles Encoding injective
-- statement:
--   The either-bad encoding is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1290-L1297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1290-L1297

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
omit [Fintype R']

theorem QEC.Coding.ProductExpansion.badChecksDistanceOrRectanglesEncoding_injective
    (h' : Matrix R' W F) (d s m k : Nat) :
    Function.Injective
      (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k) := by sorry
