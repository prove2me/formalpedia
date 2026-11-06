-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:48.669722+00:00
-- url     : https://prove2.me/theorems/9b1c243b-f5f9-47d6-b9dd-74d1d7f12bba
-- title:
--   Global Place: mem completed Integral Idele Subgroup iff nonintegral Places subset
-- statement:
--   An idele is integral away from `S` exactly when all of its nonintegral
--   places lie in `S`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L211-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L211-L226

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff_nonintegralPlaces_subset
    (S : Finset (GlobalPlace k F))
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedIntegralIdeleSubgroup S ↔
      ideleNonintegralPlaces x ⊆ S := by sorry
