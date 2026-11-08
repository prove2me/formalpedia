-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_rightRegular_lpsTannerGroupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.rightRegular_lpsTannerGroupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:42:13.674489+00:00
-- url     : https://prove2.me/theorems/2b108473-abc5-4108-ac23-ea673ead4a82
-- title:
--   LPSQuotient Tanner: right Regular lps Tanner Group Algebra Matrix
-- statement:
--   Entrywise, the right-regular expansion of the compressed matrix is the
--   actual Tanner coefficient matrix in free-orbit coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L310-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L310-L323

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSQuotientTanner
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open Cyclic FreeOrbitCoordinates LPSTanner LPSArithmetic LPSGraph
open PKDistance

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.rightRegular_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (ro : CheckOrbit401 q) (co : EdgeOrbit401 q hq)
    (go gi : CyclicGroup q) :
    LiftedProduct.rightRegularMatrix
        (lpsTannerGroupAlgebraMatrix q hq40 hq ro co) go gi =
      tannerCoefficient q hq40 hq
        ((freeOrbitEquiv (CyclicGroup q) (Check401 q)).symm (ro, go))
        ((freeOrbitEquiv (CyclicGroup q) (Edge401 q hq)).symm (co, gi)) := by sorry
