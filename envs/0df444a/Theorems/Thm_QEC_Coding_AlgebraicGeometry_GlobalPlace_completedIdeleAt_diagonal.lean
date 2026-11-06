-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIdeleAt_diagonal
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:32.18736+00:00
-- url     : https://prove2.me/theorems/2d803eba-9da1-40be-989c-27988ec410a9
-- title:
--   Global Place: completed Idele At diagonal
-- statement:
--   Local evaluation of the global idele diagonal is the corresponding local
--   completion embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L158-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L158-L162

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_diagonal (u : Fˣ) (P : GlobalPlace k F) :
    completedIdeleAt (k := k) (F := F) P
        (completedIdeleDiagonal (k := k) (F := F) u) =
      P.completionUnitsEmbedding u := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_diagonal
