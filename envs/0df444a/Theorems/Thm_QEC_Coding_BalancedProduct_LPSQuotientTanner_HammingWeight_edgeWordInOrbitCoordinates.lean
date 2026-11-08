-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_HammingWeight_edgeWordInOrbitCoordinates
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.HammingWeight_edgeWordInOrbitCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:09.884765+00:00
-- url     : https://prove2.me/theorems/3ce12870-69a3-4f64-a0fa-1a5b94396ee2
-- title:
--   LPSQuotient Tanner: Hamming Weight edge Word In Orbit Coordinates
-- statement:
--   The LPSQuotient Tanner construction uses the Hamming Weight edge Word In Orbit Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L400-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L400-L406

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.HammingWeight_edgeWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    HammingWeight (edgeWordInOrbitCoordinates q hq x) = HammingWeight x := by sorry
