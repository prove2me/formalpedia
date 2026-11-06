-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedAdeleUnitsEquivIdele_map_completedDiagonal
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_map_completedDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:14.236666+00:00
-- url     : https://prove2.me/theorems/ac8add75-b300-41e8-8b55-58531b548f65
-- title:
--   Global Place: completed Adele Units Equiv Idele map completed Diagonal
-- statement:
--   The idelic diagonal is exactly the image of the adelic diagonal on units;
--   the adele and idele constructions therefore share one global embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L147-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L147-L153

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_map_completedDiagonal (u : Fˣ) :
    completedAdeleUnitsEquivIdele (k := k) (F := F)
        (Units.map (completedDiagonal (k := k) (F := F)).toMonoidHom u) =
      completedIdeleDiagonal (k := k) (F := F) u := by sorry
