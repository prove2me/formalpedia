-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_boundary_expansion
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_boundary_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:34:58.95113+00:00
-- url     : https://prove2.me/theorems/9f251c11-89af-4fd2-9ee0-d9377d88cb66
-- title:
--   LPSQuotient Tanner: lps Tanner Action boundary expansion
-- statement:
--   The proved primal LPS Tanner expansion transported to the exact
--   group-algebra `tannerAction` used by the PK distance theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L517-L544
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L517-L544

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_boundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    LinearMap.SmallSetExpandingAtRelativeRadius
      (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq))
      1 10000000 44 41123 := by sorry
