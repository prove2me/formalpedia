-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffDimension_mono_add
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_mono_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:10.092196+00:00
-- url     : https://prove2.me/theorems/55b66b26-12d3-49e0-b416-4e0e8084b72b
-- title:
--   Global Place: global Adele Filter Diff Dimension mono add
-- statement:
--   Dimensions of comparable intrinsic adele filtration quotients add through
--   an intermediate divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleEffectiveIncrement.lean#L234-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleEffectiveIncrement.lean#L234-L281

import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterAddCommGroup
attribute [local instance] globalAdeleFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterModule
attribute [local instance] globalAdeleFilterModule

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_mono_add
    {D M N : Divisor (GlobalPlace k F)} (hDM : D ≤ M) (hMN : M ≤ N) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D N =
      globalAdeleFilterDiffDimension (k := k) (F := F) D M +
        globalAdeleFilterDiffDimension (k := k) (F := F) M N := by sorry
