-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_prefix_tail
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_prefix_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:24:33.38577+00:00
-- url     : https://prove2.me/theorems/c7ad67df-a4e7-4b0a-9d08-959017b11ad5
-- title:
--   BDL26 Connected Syndrome Mass: actual prefix tail
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the actual prefix tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L485-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L485-L492

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_prefix_tail (S : OddScale) (depth L U : ℕ) (t : ℝ) (hq : ratio S t<1) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        QEC.Locality.WeightedConnectedSetMass.structuralEnvelope (alphabet S) (envelope S t) (structural S depth).card L U := by sorry
