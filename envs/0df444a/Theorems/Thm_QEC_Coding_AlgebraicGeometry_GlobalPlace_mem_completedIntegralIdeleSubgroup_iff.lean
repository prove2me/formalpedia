-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_mem_completedIntegralIdeleSubgroup_iff
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:37.139801+00:00
-- url     : https://prove2.me/theorems/0a57e3dc-859c-4741-b0b8-b9fc2c75a8d4
-- title:
--   Global Place: mem completed Integral Idele Subgroup iff
-- statement:
--   The Global Place construction uses the mem completed Integral Idele Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L194-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L194-L199

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.mem_completedIntegralIdeleSubgroup_iff
    (S : Finset (GlobalPlace k F))
    (x : CompletedGlobalIdele (k := k) (F := F)) :
    x ∈ completedIntegralIdeleSubgroup S ↔
      ∀ P, P ∉ S → x P ∈ P.LocalUnitGroup := by sorry
