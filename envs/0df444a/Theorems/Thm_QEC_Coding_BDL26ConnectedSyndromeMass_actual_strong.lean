-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_strong
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_strong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:10:26.683797+00:00
-- url     : https://prove2.me/theorems/a420f602-97e5-4083-b5a1-bebe9639fdee
-- title:
--   BDL26 Connected Syndrome Mass: actual strong
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the actual strong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L476-L483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L476-L483

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_strong (S : OddScale) (depth m : ℕ) (t : ℝ) (hq : ratio S t<1) :
    actualMass S depth m t≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*alphabet S^m*
        envelope S t^(max 1 (m-(structural S depth).card)) := by sorry
