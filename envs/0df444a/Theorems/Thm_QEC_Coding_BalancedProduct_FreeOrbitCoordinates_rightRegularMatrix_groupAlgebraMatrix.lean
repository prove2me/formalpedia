-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_rightRegularMatrix_groupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.FreeOrbitCoordinates.rightRegularMatrix_groupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:38:43.894273+00:00
-- url     : https://prove2.me/theorems/28f07d23-5f88-4956-bb93-8b0773242552
-- title:
--   Free Orbit Coordinates: right Regular Matrix group Algebra Matrix
-- statement:
--   The compressed matrix recovers the original matrix in free-orbit
--   coordinates.  This is the exact relative-coordinate convention used by
--   `LiftedProduct.rightRegularMatrix`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L124-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L124-L135

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

theorem QEC.Coding.BalancedProduct.FreeOrbitCoordinates.rightRegularMatrix_groupAlgebraMatrix
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (ro : OrbitIndex G R) (co : OrbitIndex G C) (go gi : G) :
    QEC.Coding.LiftedProduct.rightRegularMatrix
        (groupAlgebraMatrix G P ro co) go gi =
      P ((freeOrbitEquiv G R).symm (ro, go))
        ((freeOrbitEquiv G C).symm (co, gi)) := by sorry
