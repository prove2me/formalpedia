-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_word
-- name    : QEC.Coding.BDL26RXCohomology.normalized_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:17:20.906451+00:00
-- url     : https://prove2.me/theorems/fbde93d3-b297-446f-afdc-5a0010575a82
-- title:
--   BDL26 RXCohomology: normalized word
-- statement:
--   A normalized actual cocycle is the literal map1 on its full word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L87-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L87-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCohomology.normalized_word (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word Field (RX1 P S))
    (hw : rxCoboundary1 P S w = 0)
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) :
    rxMap1Coord P S (coarseWord P S w) = w := by sorry
