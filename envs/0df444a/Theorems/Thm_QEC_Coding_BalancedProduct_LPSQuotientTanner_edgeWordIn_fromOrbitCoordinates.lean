-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_edgeWordIn_fromOrbitCoordinates
-- name    : QEC.Coding.BalancedProduct.LPSQuotientTanner.edgeWordIn_fromOrbitCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:32:22.089335+00:00
-- url     : https://prove2.me/theorems/97db7ce8-44f0-42a6-939c-efee6632dad5
-- title:
--   LPSQuotient Tanner: edge Word In from Orbit Coordinates
-- statement:
--   The LPSQuotient Tanner construction uses the edge Word In from Orbit Coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L392-L398
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSQuotientTanner.lean#L392-L398

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

theorem QEC.Coding.BalancedProduct.LPSQuotientTanner.edgeWordIn_fromOrbitCoordinates
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (z : Word (ZMod 2) (EdgeOrbit401 q hq × CyclicGroup q)) :
    edgeWordInOrbitCoordinates q hq (edgeWordFromOrbitCoordinates q hq z) = z := by sorry
