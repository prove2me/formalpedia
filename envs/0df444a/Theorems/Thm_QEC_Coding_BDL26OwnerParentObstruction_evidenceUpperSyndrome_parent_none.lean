-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_evidenceUpperSyndrome_parent_none
-- name    : QEC.Coding.BDL26OwnerParentObstruction.evidenceUpperSyndrome_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:18:01.7819+00:00
-- url     : https://prove2.me/theorems/1009474c-dc93-4e35-b992-29def2667622
-- title:
--   BDL26 Owner Parent Obstruction: evidence Upper Syndrome parent none
-- statement:
--   All nonzero upper syndrome owners are unparented in the unchanged intrinsic graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L349-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L349-L366

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

theorem QEC.Coding.BDL26OwnerParentObstruction.evidenceUpperSyndrome_parent_none
    (target : RZZ (rxReplacementPresentation evidenceStateTwo.presentation scaleFive) scaleFive)
    (h : evidenceUpperSyndrome target ≠ 0) :
    rxParent evidenceStateTwo.presentation scaleFive
      (.z (rzSyndromeOwner (rxReplacementPresentation evidenceStateTwo.presentation scaleFive)
        scaleFive target)) = none := by sorry
