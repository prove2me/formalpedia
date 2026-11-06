-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_add_placeDivisor_le
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_add_placeDivisor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:33.781193+00:00
-- url     : https://prove2.me/theorems/7b2fbfa1-a965-427a-8d46-04a928aa7b74
-- title:
--   Global Place: riemann Roch Dimension add place Divisor le
-- statement:
--   Enlarging an actual all-place Riemann--Roch divisor by one place raises
--   its dimension by at most the residue degree of that place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrementDimension.lean#L48-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrementDimension.lean#L48-L73

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_add_placeDivisor_le
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    [FiniteDimensional k (riemannRochSubmodule G)]
    [FiniteDimensional k (riemannRochSubmodule (G + placeDivisor P))] :
    riemannRochDimension (G + placeDivisor P) ≤
      riemannRochDimension G + residueDegree (k := k) (F := F) P := by sorry
