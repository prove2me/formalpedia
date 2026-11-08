-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerAction_lpsTannerGroupAlgebraMatrix
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerAction_lpsTannerGroupAlgebraMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:28.779001+00:00
-- url     : https://prove2.me/theorems/6eb8a25b-102d-4823-95a3-4f843d948673
-- title:
--   LPSQuotient Tanner: tanner Action lps Tanner Group Algebra Matrix
-- statement:
--   The horizontal `tannerAction` of the compressed group-algebra matrix is
--   definitionally the concrete Tanner boundary after the proved orbit
--   reindexings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L444-L465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L444-L465

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerAction_lpsTannerGroupAlgebraMatrix
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    tannerAction (lpsTannerGroupAlgebraMatrix q hq40 hq)
        (edgeWordInOrbitCoordinates q hq x) =
      checkWordInOrbitCoordinates q (tannerBoundary q hq40 hq x) := by sorry
