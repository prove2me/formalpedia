-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationBound_space_mono
-- name    : QEC.Coding.AlgebraicGeometry.ValuationBound.space_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:44:40.159189+00:00
-- url     : https://prove2.me/theorems/18861351-d2c8-4363-bf07-8870420bd2a7
-- title:
--   Valuation Bound: space mono
-- statement:
--   Increasing a divisor bound enlarges the associated valuation-bound space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/ValuationBound.lean#L52-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/ValuationBound.lean#L52-L55

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.FieldTheory.Finite.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_ValuationBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
open QEC.Coding.AlgebraicGeometry.ValuationBound
variable {k F P : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.ValuationBound.space_mono (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    (hGH : G ≤ H) : space (k := k) valuations G ≤ space (k := k) valuations H := by sorry
