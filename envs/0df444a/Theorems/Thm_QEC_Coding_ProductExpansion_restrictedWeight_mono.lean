-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_mono
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:42.243852+00:00
-- url     : https://prove2.me/theorems/f12db558-214d-40f1-9140-58f5657d5574
-- title:
--   Product Expansion: restricted Weight mono
-- statement:
--   Restricting either side of a rectangle cannot increase its weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L375-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L375-L391

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
omit [Fintype F] [Fintype W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.restrictedWeight_mono
    (x : Matrix W W F) {A A' B B' : Finset W}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    restrictedWeight x A' B' ≤ restrictedWeight x A B := by sorry
