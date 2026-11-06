-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:10:32.128207+00:00
-- url     : https://prove2.me/theorems/74ea6073-cb79-439b-9679-f7603f8fb120
-- title:
--   Global Place: order mul
-- statement:
--   Orders add on nonzero products, by valuation multiplicativity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L72-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L72-L78

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.order_mul (P : GlobalPlace k F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    order P (f * g) = order P f + order P g := by sorry
