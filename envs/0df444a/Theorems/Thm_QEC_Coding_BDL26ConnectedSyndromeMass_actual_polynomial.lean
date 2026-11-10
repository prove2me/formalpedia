-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_polynomial
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.actual_polynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:12:14.360252+00:00
-- url     : https://prove2.me/theorems/1b5ff3d9-de9b-42ba-a4b2-0415c8253477
-- title:
--   BDL26 Connected Syndrome Mass: actual polynomial
-- statement:
--   All-real-t actual polynomial envelope, without smallness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L456-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L456-L463

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.actual_polynomial (S : OddScale) (depth m : ℕ) (t : ℝ) :
    0≤actualMass S depth m t ∧ actualMass S depth m t≤
      ((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        (alphabet S*(1+envelope S t))^m := by sorry
