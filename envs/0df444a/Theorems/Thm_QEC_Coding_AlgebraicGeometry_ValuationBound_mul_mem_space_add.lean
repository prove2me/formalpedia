-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationBound_mul_mem_space_add
-- name    : QEC.Coding.AlgebraicGeometry.ValuationBound.mul_mem_space_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:00.857663+00:00
-- url     : https://prove2.me/theorems/929ad780-9be3-422c-9a63-c581af4bd43e
-- title:
--   Valuation Bound: mul mem space add
-- statement:
--   Product closure follows directly from valuation multiplicativity and
--   additivity of the divisor bound; it does not use Riemann--Roch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/ValuationBound.lean#L59-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/ValuationBound.lean#L59-L71

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

theorem QEC.Coding.AlgebraicGeometry.ValuationBound.mul_mem_space_add (valuations : P → Valuation F ℤᵐ⁰) {G H : Divisor P}
    {f g : F} (hf : f ∈ space (k := k) valuations G)
    (hg : g ∈ space (k := k) valuations H) :
    f * g ∈ space (k := k) valuations (G + H) := by sorry
