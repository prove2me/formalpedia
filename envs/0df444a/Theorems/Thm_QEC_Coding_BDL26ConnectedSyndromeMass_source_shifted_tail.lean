-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_source_shifted_tail
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.source_shifted_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:26:43.299012+00:00
-- url     : https://prove2.me/theorems/acf5a892-200a-48a2-b5b7-d3518d0fce99
-- title:
--   BDL26 Connected Syndrome Mass: source shifted tail
-- statement:
--   The original beta/4 substitution retains precisely the same smallness domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L526-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L526-L531

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.source_shifted_tail (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (beta : ℝ) (hq : ratio S (beta/4)<1) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m (beta/4)) L U≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S (beta/4)^(L-10)/(1-ratio S (beta/4)) := by sorry
