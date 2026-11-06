-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_isOpen_completedEverywhereIntegralIdeleSubgroup
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedEverywhereIntegralIdeleSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:26:45.750562+00:00
-- url     : https://prove2.me/theorems/b94783dc-415b-4f75-bb06-2672f46b83df
-- title:
--   Global Place: is Open completed Everywhere Integral Idele Subgroup
-- statement:
--   In particular, the everywhere-integral idele subgroup is open.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L253-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L253-L256

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedEverywhereIntegralIdeleSubgroup :
    IsOpen (completedEverywhereIntegralIdeleSubgroup (k := k) (F := F) :
      Set (CompletedGlobalIdele (k := k) (F := F))) := by sorry
