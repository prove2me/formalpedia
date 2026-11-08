-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_quotientTanner_middleCycleCode_exists_nonzero
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_middleCycleCode_exists_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:42.373548+00:00
-- url     : https://prove2.me/theorems/3e8583d7-be49-4eca-b576-3b1967f1e29c
-- title:
--   LPSQuotient Tanner: quotient Tanner middle Cycle Code exists nonzero
-- statement:
--   The LPSQuotient Tanner construction uses the quotient Tanner middle Cycle Code exists nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L946-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L946-L965

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.quotientTanner_middleCycleCode_exists_nonzero
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    ∃ x : Word (ZMod 2) (EdgeOrbit401 q hq),
      x ∈ (HorizontalSubsystem.quotientTannerComplex
        (lpsTannerGroupAlgebraMatrix q hq40 hq)).middleCycleCode.carrier ∧
      x ≠ 0 := by sorry
