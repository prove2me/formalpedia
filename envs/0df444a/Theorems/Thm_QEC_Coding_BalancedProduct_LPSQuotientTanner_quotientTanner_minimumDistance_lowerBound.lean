-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_quotientTanner_minimumDistance_lowerBound
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_minimumDistance_lowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:00.876202+00:00
-- url     : https://prove2.me/theorems/f8a35201-7219-4f50-99bc-c1dd737d2548
-- title:
--   LPSQuotient Tanner: quotient Tanner minimum Distance lower Bound
-- statement:
--   Any attained quotient Tanner minimum is at least the explicit orbit-scale
--   lower bound forced by the proved LPS expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L625-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L625-L641

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_minimumDistance_lowerBound
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    {actualDistance : Nat}
    (hMinimum : MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode
          actualDistance) :
    Fintype.card (EdgeOrbit401 q hq) / 10000000 ≤ actualDistance := by sorry
