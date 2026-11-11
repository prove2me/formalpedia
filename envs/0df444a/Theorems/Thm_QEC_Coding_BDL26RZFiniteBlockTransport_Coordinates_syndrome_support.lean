-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_syndrome_support
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.syndrome_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:19:20.524843+00:00
-- url     : https://prove2.me/theorems/db76dfd3-7b83-4b41-bb94-22c4a3a5ffd0
-- title:
--   Coordinates: syndrome support
-- statement:
--   Actual incidence, including every outgoing Q-to-Z term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L164-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L164-L184

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.syndrome_support (A : TannerSquareAdmissibleV4 P)
    (Q0 : Finset P.Q) (Z0 : Finset P.Z) (w : Word BDL26FiniteTannerSquare.Field (RZQ P S))
    (hw : hammingSupport w ⊆ inputBlocks P S Q0 Z0) :
    hammingSupport (rzCoboundary1 P A S w) ⊆ syndromeBlocks P S (zplus P Q0 Z0) := by sorry
