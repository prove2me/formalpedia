-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_order_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:17.424674+00:00
-- url     : https://prove2.me/theorems/f0f80e80-97fa-47c5-8e08-d4d053a3213f
-- title:
--   Global Place: regular At iff order nonnegative
-- statement:
--   For a nonzero function, regularity is the nonnegative order condition.
--   This is the sign convention used later in the valuation-bound RR submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L123-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/GlobalPlace.lean#L123-L128

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.regularAt_iff_order_nonnegative (P : GlobalPlace k F) {f : F} (hf : f ≠ 0) :
    RegularAt P f ↔ 0 ≤ order P f := by sorry
