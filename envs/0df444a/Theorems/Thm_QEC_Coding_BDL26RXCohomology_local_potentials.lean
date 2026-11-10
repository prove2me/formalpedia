-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_local_potentials
-- name    : QEC.Coding.BDL26RXCohomology.local_potentials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:19:48.024653+00:00
-- url     : https://prove2.me/theorems/37e13a90-e12e-45e3-97dd-aea2f42bdc21
-- title:
--   BDL26 RXCohomology: local potentials
-- statement:
--   Construct local CX potentials from the proved zero first cohomology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L54-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L54-L68

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

theorem QEC.Coding.BDL26RXCohomology.local_potentials (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Word Field (RX1 P S)) (hw : rxCoboundary1 P S w = 0) :
    ∃ f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S),
      ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
        restrictWordLinear ((localX P S).correctionRegion x) w := by sorry
