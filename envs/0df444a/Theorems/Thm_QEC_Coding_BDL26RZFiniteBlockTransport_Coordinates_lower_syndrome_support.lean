-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_Coordinates_lower_syndrome_support
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.lower_syndrome_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:34:06.651409+00:00
-- url     : https://prove2.me/theorems/0f58f477-caf0-4f9a-ac06-c41955cebf13
-- title:
--   Coordinates: lower syndrome support
-- statement:
--   The Coordinates construction uses the lower syndrome support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L195-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L195-L206

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

theorem QEC.Coding.BDL26RZFiniteBlockTransport.Coordinates.lower_syndrome_support (Q0 : Finset P.Q) (w : Word BDL26FiniteTannerSquare.Field P.Q)
    (hw : hammingSupport w ⊆ Q0) :
    hammingSupport (tannerCoboundary1 P w) ⊆ neighborZ P Q0 := by sorry
