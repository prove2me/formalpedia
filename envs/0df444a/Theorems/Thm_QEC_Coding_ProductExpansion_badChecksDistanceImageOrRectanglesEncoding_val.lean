-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceImageOrRectanglesEncoding_val
-- name    : QEC.Coding.ProductExpansion.badChecksDistanceImageOrRectanglesEncoding_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:40.665413+00:00
-- url     : https://prove2.me/theorems/0471a4c2-4582-44a8-92cf-d055a260a2eb
-- title:
--   Product Expansion: bad Checks Distance Image Or Rectangles Encoding val
-- statement:
--   The Product Expansion construction uses the bad Checks Distance Image Or Rectangles Encoding val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1361-L1371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1361-L1371

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

theorem QEC.Coding.ProductExpansion.badChecksDistanceImageOrRectanglesEncoding_val
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceImageOrRectangles (R := R) h' d s m k) :
    Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
      (badChecksDistanceImageOrRectanglesEncoding
        (R := R) h' d s m k h) = h.1 := by sorry
