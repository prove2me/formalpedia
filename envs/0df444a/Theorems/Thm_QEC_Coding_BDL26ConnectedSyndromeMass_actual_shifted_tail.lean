-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_shifted_tail
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_shifted_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:42:33.949763+00:00
-- url     : https://prove2.me/theorems/28afa243-c378-4d4b-8b6b-0206bef6b6b6
-- title:
--   BDL26 Connected Syndrome Mass: actual shifted tail
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the actual shifted tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L494-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L494-L505

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_shifted_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (t : ℝ) (hq : ratio S t<1) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S t^(L-10)/(1-ratio S t) := by sorry
