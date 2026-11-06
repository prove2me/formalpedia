-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_isOpen_completedIntegralIdeleSubgroup
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedIntegralIdeleSubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:53.152771+00:00
-- url     : https://prove2.me/theorems/6d9bed3b-1ad7-46ee-a4f4-cd85fead0839
-- title:
--   Global Place: is Open completed Integral Idele Subgroup
-- statement:
--   Requiring integrality away from a finite set defines an open idele
--   subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L245-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/CompletedGlobalIdele.lean#L245-L250

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.isOpen_completedIntegralIdeleSubgroup
    (S : Finset (GlobalPlace k F)) :
    IsOpen (completedIntegralIdeleSubgroup (k := k) (F := F) S :
      Set (CompletedGlobalIdele (k := k) (F := F))) := by sorry
