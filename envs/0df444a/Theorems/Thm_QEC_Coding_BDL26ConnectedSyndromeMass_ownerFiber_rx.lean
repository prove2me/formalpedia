-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_rx
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rx
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:11:16.282029+00:00
-- url     : https://prove2.me/theorems/28c10c6d-d6db-46a7-ba2e-612a3213069d
-- title:
--   BDL26 Connected Syndrome Mass: owner Fiber rx
-- statement:
--   RX is the entire literal RX2 fiber, including all sum/copy constructors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L196-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L196-L202

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rx (S : OddScale) (n : ℕ) (h : (n+2)%2=1)
    (u : Vertex (state S (n+1)).presentation) :
    OwnerFiber S (n+2) u = RXFiber (state S (n+1)).presentation S u := by sorry
