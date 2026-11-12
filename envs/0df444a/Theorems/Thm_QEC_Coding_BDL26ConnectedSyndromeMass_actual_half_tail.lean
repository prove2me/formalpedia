-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_half_tail
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_half_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:25:55.196222+00:00
-- url     : https://prove2.me/theorems/8620ccd4-cdb1-4294-af79-883c2aa22dec
-- title:
--   BDL26 Connected Syndrome Mass: actual half tail
-- statement:
--   The BDL26 Connected Syndrome Mass construction uses the actual half tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L507-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L507-L523

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_half_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (t : ℝ) (hq : ratio S t≤1/2) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      2*((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S t^(L-10) := by sorry
