-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_supported_filling
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.supported_filling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:34:00.024347+00:00
-- url     : https://prove2.me/theorems/b5dbd86b-4610-4722-aff3-9b9f001c3158
-- title:
--   Coordinates: supported filling
-- statement:
--   The full potential is constructed only from Q0 graph edges and Zplus faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L303-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L303-L377

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates
variable (P : TannerSquarePresentation) (S : OddScale)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.supported_filling (A : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (w : Word BDL26FiniteTannerSquare.Field (RZQ P S)) (hc : rzCoboundary1 P A S w=0)
    (hp : rzQParity P S w=0) (hw : hammingSupport w ⊆ star P S Q0 Z0) :
    ∃ p : Word BDL26FiniteTannerSquare.Field (RZX P S), rzCoboundary0 P A S p=w ∧
      hammingSupport p ⊆ potentialStar P S Q0 Z0 := by sorry
