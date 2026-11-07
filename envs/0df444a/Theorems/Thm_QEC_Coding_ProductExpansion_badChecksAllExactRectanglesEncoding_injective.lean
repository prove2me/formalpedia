-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksAllExactRectanglesEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badChecksAllExactRectanglesEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:32.088098+00:00
-- url     : https://prove2.me/theorems/b655dea9-8d0c-4bf5-a060-b8870a489f3b
-- title:
--   Product Expansion: bad Checks All Exact Rectangles Encoding injective
-- statement:
--   The all-rectangle witness encoding retains the check matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1129-L1135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1129-L1135

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

theorem QEC.Coding.ProductExpansion.badChecksAllExactRectanglesEncoding_injective
    (h' : Matrix R' W F) (s m k : Nat) :
    Function.Injective
      (badChecksAllExactRectanglesEncoding (R := R) h' s m k) := by sorry
