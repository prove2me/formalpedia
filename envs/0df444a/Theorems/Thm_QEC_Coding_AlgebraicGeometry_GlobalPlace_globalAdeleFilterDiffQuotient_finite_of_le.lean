-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffQuotient_finite_of_le
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffQuotient_finite_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:56.47324+00:00
-- url     : https://prove2.me/theorems/3fbbc60e-8827-4968-b10f-731285ee7489
-- title:
--   Global Place: global Adele Filter Diff Quotient finite of le
-- statement:
--   Every quotient between comparable intrinsic adele filtration pieces is
--   finite-dimensional over the constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleEffectiveIncrement.lean#L216-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleEffectiveIncrement.lean#L216-L230

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffQuotient_finite_of_le
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    Module.Finite k
      (globalAdeleFilter (k := k) (F := F) E ⧸
        Submodule.comap (globalAdeleFilter (k := k) (F := F) E).subtype
          (globalAdeleFilter (k := k) (F := F) D)) := by sorry
