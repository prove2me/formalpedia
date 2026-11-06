-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_support
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:22.74879+00:00
-- url     : https://prove2.me/theorems/3226fc05-6b5b-43ce-9d91-6c731803a704
-- title:
--   Global Place: finite Place Divisor support
-- statement:
--   The support of an injective finite-family divisor is exactly the image of
--   the enumerating family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L70-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L70-L83

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_support [Fintype ι]
    (P : ι → GlobalPlace k F) (hP : Function.Injective P) :
    ↑(finitePlaceDivisor P).support = Set.range P := by sorry
