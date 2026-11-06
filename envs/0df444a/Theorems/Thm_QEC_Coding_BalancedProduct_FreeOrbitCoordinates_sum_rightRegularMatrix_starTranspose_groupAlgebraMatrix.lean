-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:47:03.577061+00:00
-- url     : https://prove2.me/theorems/f3a5ccef-c6de-4514-b7cc-5267c407d1d4
-- title:
--   Free Orbit Coordinates: sum right Regular Matrix star Transpose group Algebra Matrix
-- statement:
--   The analogous matrix-vector identity for the star-transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L165-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L165-L197

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

theorem QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
    [Fintype R] [Fintype (OrbitIndex G R)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (y : R → F)
    (co : OrbitIndex G C) (go : G) :
    (∑ ro : OrbitIndex G R, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (QEC.Coding.LiftedProduct.starTranspose
            (groupAlgebraMatrix G P) co ro) go gi *
        y ((freeOrbitEquiv G R).symm (ro, gi))) =
      ∑ r : R,
        P r ((freeOrbitEquiv G C).symm (co, go)) * y r := by sorry
