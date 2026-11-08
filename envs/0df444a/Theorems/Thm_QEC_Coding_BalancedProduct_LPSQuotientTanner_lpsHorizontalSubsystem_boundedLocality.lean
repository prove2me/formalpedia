-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_boundedLocality
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:37.91654+00:00
-- url     : https://prove2.me/theorems/31d63651-618f-4dd2-846e-d7fae510c869
-- title:
--   LPSQuotient Tanner: lps Horizontal Subsystem bounded Locality
-- statement:
--   The actual BE20 cyclic balanced product has uniform check weight and
--   variable degree at most `404 = max 400 402 + 2`.  This conclusion uses only
--   the constructed Tanner and cyclic matrices; it does not use the external LPS
--   Ramanujan assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L803-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L803-L819

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.lpsHorizontalSubsystem_boundedLocality
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    BoundedLocality
      (LiftedProduct.boundaryIncidence
        (Cyclic.liftedProductData
          (lpsTannerGroupAlgebraMatrix q hq40 hq)
          (Cyclic.cyclicGenerator q))).localityProfile
      404 := by sorry
