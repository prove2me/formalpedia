-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:09.547837+00:00
-- url     : https://prove2.me/theorems/65132753-7d79-4ee1-b8ec-699bcff02c25
-- title:
--   Global Place: global Adele Filter mono
-- statement:
--   The intrinsic adele filtration is monotone in the divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/Adele.lean#L171-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/Adele.lean#L171-L175

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilter_mono {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleFilter (k := k) (F := F) D ≤
      globalAdeleFilter (k := k) (F := F) E := by sorry
