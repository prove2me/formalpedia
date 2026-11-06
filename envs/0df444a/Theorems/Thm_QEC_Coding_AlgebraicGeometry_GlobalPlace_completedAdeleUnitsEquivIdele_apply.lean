-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedAdeleUnitsEquivIdele_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:47.085345+00:00
-- url     : https://prove2.me/theorems/95465773-13cc-41bc-8900-52b3cbe4a60c
-- title:
--   Global Place: completed Adele Units Equiv Idele apply
-- statement:
--   The Global Place construction uses the completed Adele Units Equiv Idele apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L131-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L131-L135

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_apply
    (x : (CompletedGlobalAdele (k := k) (F := F))ˣ)
    (P : GlobalPlace k F) :
    completedAdeleUnitsEquivIdele (k := k) (F := F) x P = x.1 P := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedAdeleUnitsEquivIdele_apply
