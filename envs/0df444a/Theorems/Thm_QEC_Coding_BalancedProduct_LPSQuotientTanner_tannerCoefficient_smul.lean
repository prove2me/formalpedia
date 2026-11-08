-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_tannerCoefficient_smul
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerCoefficient_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:06.847994+00:00
-- url     : https://prove2.me/theorems/db72740c-1c8d-4077-89a9-f52e1b2d9754
-- title:
--   LPSQuotient Tanner: tanner Coefficient smul
-- statement:
--   The LPSQuotient Tanner construction uses the tanner Coefficient smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L265-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L265-L286

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.tannerCoefficient_smul
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (h : CyclicGroup q) (c : Check401 q) (e : Edge401 q hq) :
    tannerCoefficient q hq40 hq (h • c) (h • e) =
      tannerCoefficient q hq40 hq c e := by sorry
