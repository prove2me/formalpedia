-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsTannerAction_starTranspose_basis_weight_le
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_starTranspose_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:53.818191+00:00
-- url     : https://prove2.me/theorems/e81d8e05-f976-4269-b8db-618851af5d6a
-- title:
--   LPSQuotient Tanner: lps Tanner Action star Transpose basis weight le
-- statement:
--   Every column of the star-transposed compressed Tanner action has weight at
--   most the graph degree `402`; no matrix sparsity is supplied externally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L759-L797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L759-L797

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsTannerAction_starTranspose_basis_weight_le
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (i : CheckOrbit401 q × CyclicGroup q) :
    HammingWeight
      (tannerAction (LiftedProduct.starTranspose
        (lpsTannerGroupAlgebraMatrix q hq40 hq)) (Pi.single i 1)) ≤ 402 := by sorry
