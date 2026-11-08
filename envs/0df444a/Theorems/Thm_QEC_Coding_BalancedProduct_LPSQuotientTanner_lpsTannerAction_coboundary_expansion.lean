-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_coboundary_expansion
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_coboundary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:35:51.378342+00:00
-- url     : https://prove2.me/theorems/3a634a06-3b15-42bb-b6e0-14d74f7fd210
-- title:
--   LPSQuotient Tanner: lps Tanner Action coboundary expansion
-- statement:
--   The proved transpose LPS Tanner expansion transported to the exact
--   star-transposed group-algebra action used by the dual PK cases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L548-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L548-L577

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_coboundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    LinearMap.SmallSetExpandingAtRelativeRadius
      (tannerAction (LiftedProduct.starTranspose
        (lpsTannerGroupAlgebraMatrix q hq40 hq)))
      1 10000000 11 102500 := by sorry
