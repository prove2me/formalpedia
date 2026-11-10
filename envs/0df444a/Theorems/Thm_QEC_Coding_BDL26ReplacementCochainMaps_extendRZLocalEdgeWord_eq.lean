-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_extendRZLocalEdgeWord_eq
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.extendRZLocalEdgeWord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:12:43.951561+00:00
-- url     : https://prove2.me/theorems/25e84580-591a-4452-a6ef-86d05842f057
-- title:
--   BDL26 Replacement Cochain Maps: extend RZLocal Edge Word eq
-- statement:
--   The pushforward and constructor forms of the local-edge embedding agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L644-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L644-L657

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.extendRZLocalEdgeWord_eq
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z)
    (word : Word Field (ZDoubleCylinderEdge P z S)) :
    extendRZLocalEdgeWord P S z word = extendZEdgeWord P S z word := by sorry
