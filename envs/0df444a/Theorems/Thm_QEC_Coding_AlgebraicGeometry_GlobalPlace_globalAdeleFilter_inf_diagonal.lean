-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_inf_diagonal
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_inf_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:17.853406+00:00
-- url     : https://prove2.me/theorems/ecfa3f83-c6f8-4ba5-aa6b-f6ed9e237b7b
-- title:
--   Global Place: global Adele Filter inf diagonal
-- statement:
--   Intersecting an adele filtration piece with the diagonal recovers the
--   actual all-place Riemann--Roch submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/Adele.lean#L158-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/Adele.lean#L158-L168

import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Filter.Cofinite
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_inf_diagonal (D : Divisor (GlobalPlace k F)) :
    globalAdeleFilter (k := k) (F := F) D ⊓
        diagonalAdeleSubmodule (k := k) (F := F) =
      Submodule.map (diagonalAdele (k := k) (F := F)) (riemannRochSubmodule D) := by sorry
