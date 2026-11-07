-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceOrRectanglesEncoding_val
-- name    : QEC.Coding.ProductExpansion.badChecksDistanceOrRectanglesEncoding_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:29.430166+00:00
-- url     : https://prove2.me/theorems/9ebbea65-9d2e-4ab9-9a6e-d7b83d5e722c
-- title:
--   Product Expansion: bad Checks Distance Or Rectangles Encoding val
-- statement:
--   The either-bad encoding retains the underlying check matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1279-L1286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1279-L1286

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

theorem QEC.Coding.ProductExpansion.badChecksDistanceOrRectanglesEncoding_val
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceOrRectangles (R := R) h' d s m k) :
    Sum.elim Subtype.val Subtype.val
      (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k h) = h.1 := by sorry
