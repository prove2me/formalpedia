-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_raw_boundary_iff
-- name    : QEC.Coding.BDL26RXCohomology.raw_boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:16:25.672675+00:00
-- url     : https://prove2.me/theorems/0da42eaa-f505-4f03-b33c-66d646404948
-- title:
--   BDL26 RXCohomology: raw boundary iff
-- statement:
--   No supplied boundary implication: actual connectedness recovers an old
--   potential whenever the literal map1 word is an actual full coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L140-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L140-L158

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

theorem QEC.Coding.BDL26RXCohomology.raw_boundary_iff (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (v : Word Field P.Q) :
    (∃ f, rxCoboundary0 P S f = rxMap1Coord P S v) ↔
      ∃ old, tannerCoboundary0 P old = v := by sorry
