-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_normalized_cocycle
-- name    : QEC.Coding.BDL26RXCohomology.normalized_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:29:08.902944+00:00
-- url     : https://prove2.me/theorems/015b9fce-c4a5-4dc3-8239-6bb42b70f85f
-- title:
--   BDL26 RXCohomology: normalized cocycle
-- statement:
--   The old word recovered from a normalized cocycle is itself a cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L108-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L108-L118

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

theorem QEC.Coding.BDL26RXCohomology.normalized_cocycle (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (w : Word Field (RX1 P S))
    (hw : rxCoboundary1 P S w = 0)
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w = 0) :
    tannerCoboundary1 P (coarseWord P S w) = 0 := by sorry
