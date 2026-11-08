-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_quotientTanner_middleHomology_finrank_lowerBound
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_middleHomology_finrank_lowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:07.009098+00:00
-- url     : https://prove2.me/theorems/f9e9a75b-0d54-4585-a40c-78f8c42ba63e
-- title:
--   LPSQuotient Tanner: quotient Tanner middle Homology finrank lower Bound
-- statement:
--   Rank-nullity for the actual quotient Tanner boundary gives the source
--   dimension lower bound.  No independence or full-rank property of the checks
--   is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L877-L908
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L877-L908

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_middleHomology_finrank_lowerBound
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (EdgeOrbit401 q hq) - Fintype.card (CheckOrbit401 q) ≤
      Module.finrank (ZMod 2)
        (HorizontalSubsystem.quotientTannerComplex
          (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleHomology := by sorry
