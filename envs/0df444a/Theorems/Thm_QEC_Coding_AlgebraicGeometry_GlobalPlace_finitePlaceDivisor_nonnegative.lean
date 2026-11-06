-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:07.535401+00:00
-- url     : https://prove2.me/theorems/511104e2-8be4-410d-a029-c2db14a96dbb
-- title:
--   Global Place: finite Place Divisor nonnegative
-- statement:
--   A finite-family place divisor is coefficientwise nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L59-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L59-L66

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_nonnegative [Fintype ι]
    (P : ι → GlobalPlace k F) : 0 ≤ finitePlaceDivisor P := by sorry
