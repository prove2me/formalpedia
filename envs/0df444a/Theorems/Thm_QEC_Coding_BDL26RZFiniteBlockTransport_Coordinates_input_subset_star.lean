-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_input_subset_star
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.input_subset_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:33:53.95205+00:00
-- url     : https://prove2.me/theorems/2042148f-0bc1-4f44-9af6-5705c6511343
-- title:
--   Coordinates: input subset star
-- statement:
--   The Coordinates construction uses the input subset star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L152-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L152-L158

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.input_subset_star (Q0 : Finset P.Q) (Z0 : Finset P.Z) :
    inputBlocks P S Q0 Z0 ⊆ star P S Q0 Z0 := by sorry
