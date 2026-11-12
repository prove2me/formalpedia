-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_physicalXStar_face_iff
-- name    : QEC.Coding.BDL26RXPhysicalStarTransport.physicalXStar_face_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:05:05.692507+00:00
-- url     : https://prove2.me/theorems/f4423107-fd92-4611-9f98-f91535d8172a
-- title:
--   BDL26 RXPhysical Star Transport: physical XStar face iff
-- statement:
--   Face existence is reconstructed by the actual perfect pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L35-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean#L35-L47

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPhysicalStarTransport.physicalXStar_face_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (x : P.X) (q : P.Q) :
    q ∈ physicalXStar P x ↔ ∃ f : P.Face, ∃ c : Fin 2,
      P.faceX f=x ∧ P.faceQ f c=q := by sorry
