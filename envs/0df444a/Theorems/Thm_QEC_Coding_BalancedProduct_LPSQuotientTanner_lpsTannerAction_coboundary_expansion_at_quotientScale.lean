-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_coboundary_expansion_at_quotientScale
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_coboundary_expansion_at_quotientScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:37:43.889684+00:00
-- url     : https://prove2.me/theorems/04a400c1-b5d1-4f64-8488-319fb89d0e6c
-- title:
--   LPSQuotient Tanner: lps Tanner Action coboundary expansion at quotient Scale
-- statement:
--   The transpose relative expansion at the quotient check-orbit scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L688-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L688-L713

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_coboundary_expansion_at_quotientScale
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerAction (LiftedProduct.starTranspose
      (lpsTannerGroupAlgebraMatrix q hq40 hq))).SmallSetExpanding
        (q * (Fintype.card (CheckOrbit401 q) / 10000000)) 11 102500 := by sorry
