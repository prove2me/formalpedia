-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffDimension_add_placeDivisor
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_add_placeDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:51.050796+00:00
-- url     : https://prove2.me/theorems/b7f47bf8-6622-4cf3-8aea-25684d158a1c
-- title:
--   Global Place: global Adele Filter Diff Dimension add place Divisor
-- statement:
--   The one-place intrinsic adele quotient has dimension equal to the actual
--   residue degree of its supporting place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdelePlaceIncrement.lean#L238-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdelePlaceIncrement.lean#L238-L262

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_add_placeDivisor
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (D + placeDivisor P) =
      residueDegree (k := k) (F := F) P := by sorry
