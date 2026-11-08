-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_checkWordIn_fromOrbitCoordinates
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.checkWordIn_fromOrbitCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:23.656587+00:00
-- url     : https://prove2.me/theorems/28c90669-b48a-4eae-8beb-4844075e21de
-- title:
--   LPSQuotient Tanner: check Word In from Orbit Coordinates
-- statement:
--   The LPSQuotient Tanner construction uses the check Word In from Orbit Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L377-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L377-L382

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.checkWordIn_fromOrbitCoordinates
    (q : ℕ)
    (z : Word (ZMod 2) (CheckOrbit401 q × CyclicGroup q)) :
    checkWordInOrbitCoordinates q (checkWordFromOrbitCoordinates q z) = z := by sorry
