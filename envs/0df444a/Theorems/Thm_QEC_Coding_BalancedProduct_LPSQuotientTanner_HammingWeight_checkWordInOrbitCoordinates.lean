-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_HammingWeight_checkWordInOrbitCoordinates
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.HammingWeight_checkWordInOrbitCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:13.35412+00:00
-- url     : https://prove2.me/theorems/8c6e5417-bdbb-4dc0-9cb8-0fd28381f69a
-- title:
--   LPSQuotient Tanner: Hamming Weight check Word In Orbit Coordinates
-- statement:
--   The LPSQuotient Tanner construction uses the Hamming Weight check Word In Orbit Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L408-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L408-L413

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.HammingWeight_checkWordInOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight (checkWordInOrbitCoordinates q y) = HammingWeight y := by sorry
