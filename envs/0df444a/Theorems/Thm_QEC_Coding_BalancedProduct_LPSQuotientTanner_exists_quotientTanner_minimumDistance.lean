-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_exists_quotientTanner_minimumDistance
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.exists_quotientTanner_minimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:37.679016+00:00
-- url     : https://prove2.me/theorems/6864cecf-6020-4cf3-b649-2a7e2354ed95
-- title:
--   LPSQuotient Tanner: exists quotient Tanner minimum Distance
-- statement:
--   The LPSQuotient Tanner construction uses the exists quotient Tanner minimum Distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L967-L975
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L967-L975

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.exists_quotientTanner_minimumDistance
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    ∃ d : ℕ, MinimumDistance
      (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode d := by sorry
