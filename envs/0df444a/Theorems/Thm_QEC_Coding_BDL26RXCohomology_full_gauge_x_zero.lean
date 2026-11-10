-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCohomology_full_gauge_x_zero
-- name    : QEC.Coding.BDL26RXCohomology.full_gauge_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:19:47.295032+00:00
-- url     : https://prove2.me/theorems/02678505-1fc8-4c61-b261-6a7643f3a2df
-- title:
--   BDL26 RXCohomology: full gauge x zero
-- statement:
--   Subtract the entire actual global coboundary; every X error vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L71-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean#L71-L79

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

theorem QEC.Coding.BDL26RXCohomology.full_gauge_x_zero (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S))
    (f : ∀ x : P.X, Word Field (DoubleCylinderVertex P x S))
    (hf : ∀ x, wordLinearMapTranspose (localCx P S x).boundary1 (f x) =
      restrictWordLinear ((localX P S).correctionRegion x) w) :
    ∀ x, restrictWordLinear ((localX P S).correctionRegion x)
      (w - rxCoboundary0 P S (∑ y : P.X, xLift P S y (f y))) = 0 := by sorry
