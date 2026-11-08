-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_boundary_expansion_at_quotientScale
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_boundary_expansion_at_quotientScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:31.30037+00:00
-- url     : https://prove2.me/theorems/f453dc68-2def-4d3a-8ecb-a5277669c661
-- title:
--   LPSQuotient Tanner: lps Tanner Action boundary expansion at quotient Scale
-- statement:
--   The relative LPS expansion supplies precisely the lifted radius obtained
--   from the quotient edge-orbit scale `|E/H| / 10^7`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L597-L621
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L597-L621

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_boundary_expansion_at_quotientScale
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)).SmallSetExpanding
      (q * (Fintype.card (EdgeOrbit401 q hq) / 10000000)) 44 41123 := by sorry
