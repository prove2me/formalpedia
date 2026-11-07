-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksDistanceOrRectangles_le_add
-- name    : QEC.Coding.ProductExpansion.card_badChecksDistanceOrRectangles_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:31.386962+00:00
-- url     : https://prove2.me/theorems/f8cf5ee5-0512-44cb-b774-0a295e2300de
-- title:
--   Product Expansion: card bad Checks Distance Or Rectangles le add
-- statement:
--   Cardinal union bound for the two bad-check events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1301-L1318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1301-L1318

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

theorem QEC.Coding.ProductExpansion.card_badChecksDistanceOrRectangles_le_add
    (h' : Matrix R' W F) (d s m k : Nat) :
    Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by sorry
