-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_completedIntegralIdeleSubgroup_mono
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIntegralIdeleSubgroup_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:24.99797+00:00
-- url     : https://prove2.me/theorems/9f844402-e011-4a41-bd0d-703ac916ed30
-- title:
--   Global Place: completed Integral Idele Subgroup mono
-- statement:
--   Allowing more exceptional places weakens the integrality condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L202-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L202-L207

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIntegralIdeleSubgroup_mono
    {S T : Finset (GlobalPlace k F)} (hST : S ⊆ T) :
    completedIntegralIdeleSubgroup (k := k) (F := F) S ≤
      completedIntegralIdeleSubgroup (k := k) (F := F) T := by sorry
