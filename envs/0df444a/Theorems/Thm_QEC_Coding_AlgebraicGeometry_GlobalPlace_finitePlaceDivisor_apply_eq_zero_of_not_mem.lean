-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply_eq_zero_of_not_mem
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply_eq_zero_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:35:38.046981+00:00
-- url     : https://prove2.me/theorems/3025d8aa-6735-4168-b7bb-9bc7feb946a2
-- title:
--   Global Place: finite Place Divisor apply eq zero of not mem
-- statement:
--   A place outside the finite image has coefficient zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L46-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L46-L56

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply_eq_zero_of_not_mem [Fintype ι]
    (P : ι → GlobalPlace k F) (Q : GlobalPlace k F)
    (hQ : Q ∉ Set.range P) : finitePlaceDivisor P Q = 0 := by sorry
