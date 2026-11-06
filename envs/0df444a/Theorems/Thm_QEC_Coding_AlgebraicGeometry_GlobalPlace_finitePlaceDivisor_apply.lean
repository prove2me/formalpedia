-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:35:39.979037+00:00
-- url     : https://prove2.me/theorems/0e94f53b-8833-42cc-9774-e99f332e3815
-- title:
--   Global Place: finite Place Divisor apply
-- statement:
--   An injectively enumerated place has coefficient one in its finite-family
--   divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L34-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L34-L43

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply [Fintype ι]
    (P : ι → GlobalPlace k F) (hP : Function.Injective P) (i : ι) :
    finitePlaceDivisor P (P i) = 1 := by sorry
