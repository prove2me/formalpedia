-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_completedEverywhereIntegralIdeleSubgroup_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedEverywhereIntegralIdeleSubgroup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:34.4571+00:00
-- url     : https://prove2.me/theorems/677e130b-1e62-4f9d-8ade-b1699acd3de0
-- title:
--   Global Place: mem completed Everywhere Integral Idele Subgroup iff
-- statement:
--   Everywhere integrality is equivalent to having no nonintegral places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L234-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L234-L241

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedEverywhereIntegralIdeleSubgroup_iff
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedEverywhereIntegralIdeleSubgroup ↔
      ideleNonintegralPlaces x = ∅ := by sorry
