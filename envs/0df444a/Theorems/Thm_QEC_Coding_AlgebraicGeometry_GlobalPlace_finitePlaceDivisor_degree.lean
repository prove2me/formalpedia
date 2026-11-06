-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:19.798861+00:00
-- url     : https://prove2.me/theorems/a86f31a7-7ba3-4b81-808b-aa5fe62e9c25
-- title:
--   Global Place: finite Place Divisor degree
-- statement:
--   The weighted degree of a finite-family divisor is the sum of the actual
--   residue degrees of its places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L87-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/FinitePlaceDivisor.lean#L87-L100

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_degree [Fintype ι]
    (P : ι → GlobalPlace k F) :
    Divisor.degree (residueDegree (k := k) (F := F))
        (finitePlaceDivisor P) =
      ∑ i : ι, (residueDegree (k := k) (F := F) (P i) : ℤ) := by sorry
