-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_sum_rightRegularMatrix_groupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_groupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:52.087545+00:00
-- url     : https://prove2.me/theorems/022cb84e-bba0-4b8c-b558-435a87ecf274
-- title:
--   Free Orbit Coordinates: sum right Regular Matrix group Algebra Matrix
-- statement:
--   Matrix-vector multiplication by the right-regular expansion is exactly
--   matrix-vector multiplication by the original equivariant matrix after
--   reindexing the column coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L140-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L140-L162

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

theorem QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_groupAlgebraMatrix
    [Fintype C] [Fintype (OrbitIndex G C)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (z : C → F)
    (ro : OrbitIndex G R) (go : G) :
    (∑ co : OrbitIndex G C, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (groupAlgebraMatrix G P ro co) go gi *
        z ((freeOrbitEquiv G C).symm (co, gi))) =
      ∑ c : C,
        P ((freeOrbitEquiv G R).symm (ro, go)) c * z c := by sorry
