-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksForRectangleEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badChecksForRectangleEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:14.502844+00:00
-- url     : https://prove2.me/theorems/0b938411-8ff1-4eb2-a0c6-d5226be38475
-- title:
--   Product Expansion: bad Checks For Rectangle Encoding injective
-- statement:
--   Choosing a witness does not identify two distinct bad check matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L989-L995
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L989-L995

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

theorem QEC.Coding.ProductExpansion.badChecksForRectangleEncoding_injective
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Function.Injective
      (badChecksForRectangleEncoding (R := R) h' A B s k) := by sorry
