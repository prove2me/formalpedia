-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleLocalLeadingCoefficient_ker
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleLocalLeadingCoefficient_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:20.109893+00:00
-- url     : https://prove2.me/theorems/0e52e724-b7f8-4561-a720-19c343e5f45a
-- title:
--   Global Place: global Adele Local Leading Coefficient ker
-- statement:
--   The one-place adele leading coefficient vanishes exactly on the smaller
--   filtration piece `A(D)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdelePlaceIncrement.lean#L147-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdelePlaceIncrement.lean#L147-L175

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleLocalLeadingCoefficient_ker
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    LinearMap.ker (globalAdeleLocalLeadingCoefficient D P) =
      Submodule.comap
        (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
        (globalAdeleFilter (k := k) (F := F) D) := by sorry
