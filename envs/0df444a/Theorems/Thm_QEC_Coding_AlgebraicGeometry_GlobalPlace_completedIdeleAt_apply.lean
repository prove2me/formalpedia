-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIdeleAt_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:30.654547+00:00
-- url     : https://prove2.me/theorems/153bff1f-982d-46a4-b9e4-be44e30e0253
-- title:
--   Global Place: completed Idele At apply
-- statement:
--   The Global Place construction uses the completed Idele At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L118-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L118-L121

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_apply (P : GlobalPlace k F)
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    completedIdeleAt (k := k) (F := F) P x = x P := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleAt_apply
