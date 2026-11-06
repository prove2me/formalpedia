-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_le_add_placeDivisor
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_le_add_placeDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:34:23.089914+00:00
-- url     : https://prove2.me/theorems/075d0058-218d-4b51-9cf3-5fcc15db1102
-- title:
--   Global Place: riemann Roch Submodule le add place Divisor
-- statement:
--   Adding a nonnegative one-place divisor enlarges the corresponding
--   Riemann--Roch submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L61-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PlaceIncrement.lean#L61-L73

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_le_add_placeDivisor
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochSubmodule G ≤ riemannRochSubmodule (G + placeDivisor P) := by sorry
