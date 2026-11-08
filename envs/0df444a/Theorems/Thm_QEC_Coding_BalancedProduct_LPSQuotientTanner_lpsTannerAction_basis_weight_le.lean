-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_basis_weight_le
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:40.180766+00:00
-- url     : https://prove2.me/theorems/a80a7604-a68b-4e12-81f6-cb1e5ed30f8b
-- title:
--   LPSQuotient Tanner: lps Tanner Action basis weight le
-- statement:
--   Every column of the compressed Tanner action has weight at most `400`,
--   because an actual LPS edge meets 200 local checks at each endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L717-L755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L717-L755

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (i : EdgeOrbit401 q hq × CyclicGroup q) :
    HammingWeight
      (tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)
        (Pi.single i 1)) ≤ 400 := by sorry
