-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_interval_polynomial
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_interval_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:10:12.951777+00:00
-- url     : https://prove2.me/theorems/cd0b57b9-7fe8-4aca-b239-5ffd2166656b
-- title:
--   BDL26 Connected Syndrome Mass: actual interval polynomial
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the actual interval polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L465-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L465-L474

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_interval_polynomial (S : OddScale) (depth L U : ℕ) (t : ℝ) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U ≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        QEC.Locality.WeightedConnectedSetMass.geometric (alphabet S*(1+envelope S t)) (max 1 L) (U+1-max 1 L) := by sorry
