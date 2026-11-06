-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochPlaceLeadingCoefficient_ker
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPlaceLeadingCoefficient_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:35:08.449863+00:00
-- url     : https://prove2.me/theorems/766559c6-d7bd-4f1e-8c41-b1180415929e
-- title:
--   Global Place: riemann Roch Place Leading Coefficient ker
-- statement:
--   The one-place leading coefficient vanishes exactly on the embedded copy
--   of `L(G)` inside `L(G + P)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L181-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L181-L276

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochPlaceLeadingCoefficient_ker
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    LinearMap.ker (riemannRochPlaceLeadingCoefficient G P) =
      riemannRochPlaceIncrementSubmodule G P := by sorry
