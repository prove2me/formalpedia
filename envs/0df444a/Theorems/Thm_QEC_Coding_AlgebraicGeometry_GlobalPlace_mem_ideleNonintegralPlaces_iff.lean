-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_ideleNonintegralPlaces_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_ideleNonintegralPlaces_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:40.060376+00:00
-- url     : https://prove2.me/theorems/729bc24f-7a37-411a-8b81-9f39f2ab0080
-- title:
--   Global Place: mem idele Nonintegral Places iff
-- statement:
--   The Global Place construction uses the mem idele Nonintegral Places iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L173-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L173-L182

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_ideleNonintegralPlaces_iff
    (x : CompletedGlobalIdele (k := k) (F := F))
    (P : GlobalPlace k F) :
    P ∈ ideleNonintegralPlaces x ↔ x P ∉ P.LocalUnitGroup := by sorry
