-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_anchors_disjoint
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.anchors_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:28:31.511925+00:00
-- url     : https://prove2.me/theorems/73021f9b-7d86-4412-ab7a-e2af6502e140
-- title:
--   BDL26 Connected Syndrome Mass: anchors disjoint
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the anchors disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L414-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L414-L420

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.anchors_disjoint (S : OddScale) (depth : ℕ) :
    Disjoint (BDL26ConnectedSetCounting.levelTwoAnchors S depth) (structural S depth) := by sorry
