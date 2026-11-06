-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIdeleDiagonal_apply
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleDiagonal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:21.35163+00:00
-- url     : https://prove2.me/theorems/901f4a0d-0a11-437d-bf0c-62f24ea99732
-- title:
--   Global Place: completed Idele Diagonal apply
-- statement:
--   The Global Place construction uses the completed Idele Diagonal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L101-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L101-L104

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleDiagonal_apply (u : Fˣ) (P : GlobalPlace k F) :
    completedIdeleDiagonal (k := k) (F := F) u P =
      P.completionUnitsEmbedding u := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIdeleDiagonal_apply
