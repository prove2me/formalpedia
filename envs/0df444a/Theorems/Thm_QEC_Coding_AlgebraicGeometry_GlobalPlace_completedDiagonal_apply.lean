-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedDiagonal_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:57.267565+00:00
-- url     : https://prove2.me/theorems/a86d48ff-9a3a-4b01-88d8-79c8f22e7906
-- title:
--   Global Place: completed Diagonal apply
-- statement:
--   The Global Place construction uses the completed Diagonal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L107-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalAdele.lean#L107-L109

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuedField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply (f : F) (P : GlobalPlace k F) :
    completedDiagonal (k := k) (F := F) f P = P.completionEmbedding f := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedDiagonal_apply
