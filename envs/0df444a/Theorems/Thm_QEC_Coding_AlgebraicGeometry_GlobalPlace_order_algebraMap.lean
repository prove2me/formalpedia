-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:56:48.946784+00:00
-- url     : https://prove2.me/theorems/03708683-c8da-49e2-927a-9eea8ab748f8
-- title:
--   Global Place: order algebra Map
-- statement:
--   Every nonzero element of the finite constant field has order zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L87-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L87-L89

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.order_algebraMap (P : GlobalPlace k F) (a : k) (ha : a ≠ 0) :
    order P (algebraMap k F a) = 0 := by sorry
