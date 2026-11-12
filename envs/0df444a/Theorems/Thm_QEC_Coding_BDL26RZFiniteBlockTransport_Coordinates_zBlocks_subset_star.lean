-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_zBlocks_subset_star
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.zBlocks_subset_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:46:43.36107+00:00
-- url     : https://prove2.me/theorems/a3d2a05f-126b-4345-bc2e-5428cdcca5e3
-- title:
--   Coordinates: z Blocks subset star
-- statement:
--   The Coordinates construction uses the z Blocks subset star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L160-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L160-L161

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.zBlocks_subset_star (Q0 : Finset P.Q) (Z0 : Finset P.Z) :
    zBlocks P S (zplus P Q0 Z0) ⊆ star P S Q0 Z0 := by sorry
