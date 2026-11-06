-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_groupAlgebraMatrix_apply
-- name    : QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:38:57.615971+00:00
-- url     : https://prove2.me/theorems/8c7f0d54-72a7-4451-9fae-1cf1e322d3b7
-- title:
--   Free Orbit Coordinates: group Algebra Matrix apply
-- statement:
--   The Free Orbit Coordinates construction uses the group Algebra Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L116-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L116-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]
variable {F : Type*} [Semiring F]
variable {R : Type*} {C : Type*}
variable [MulAction G R] [MulAction G C]
variable [IsCancelSMul G R] [IsCancelSMul G C]
variable [Fintype G]

theorem QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
    (P : Matrix R C F) (ro : OrbitIndex G R) (co : OrbitIndex G C) (h : G) :
    (groupAlgebraMatrix G P ro co).coeff h =
      P (h • orbitRep G R ro) (orbitRep G C co) := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
