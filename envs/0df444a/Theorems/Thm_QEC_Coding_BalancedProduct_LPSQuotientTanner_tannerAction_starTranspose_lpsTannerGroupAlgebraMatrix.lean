-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:22.805141+00:00
-- url     : https://prove2.me/theorems/fcb77d24-43bd-40c8-a0c4-cbf934eba470
-- title:
--   LPSQuotient Tanner: tanner Action star Transpose lps Tanner Group Algebra Matrix
-- statement:
--   The star-transposed group-algebra action is the actual transpose Tanner
--   map after the same proved orbit reindexings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L469-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L469-L513

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerAction_starTranspose_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    tannerAction
        (LiftedProduct.starTranspose
          (lpsTannerGroupAlgebraMatrix q hq40 hq))
        (checkWordInOrbitCoordinates q y) =
      edgeWordInOrbitCoordinates q hq
        (wordLinearMapTranspose (tannerBoundary q hq40 hq) y) := by sorry
