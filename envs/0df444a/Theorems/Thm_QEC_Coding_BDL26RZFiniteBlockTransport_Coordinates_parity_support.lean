-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_parity_support
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.parity_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:33:22.135847+00:00
-- url     : https://prove2.me/theorems/4012e71f-7a10-4388-8748-29ea3e992439
-- title:
--   Coordinates: parity support
-- statement:
--   The Coordinates construction uses the parity support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L186-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L186-L193

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.parity_support (Q0 : Finset P.Q) (Z0 : Finset P.Z)
    (w : Word BDL26FiniteTannerSquare.Field (RZQ P S)) (hw : hammingSupport w ⊆ inputBlocks P S Q0 Z0) :
    hammingSupport (rzQParity P S w) ⊆ Q0 := by sorry
