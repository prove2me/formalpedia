-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_rz_x_empty
-- name    : QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rz_x_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:42:46.180002+00:00
-- url     : https://prove2.me/theorems/9fe39fc3-f7e6-42d2-b58b-817802ba1963
-- title:
--   BDL26 Connected Syndrome Mass: owner Fiber rz x empty
-- statement:
--   On the RZ branch X and Q owner fibers are empty, not invented syndromes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L205-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ConnectedSyndromeMass.lean#L205-L210

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

theorem QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_rz_x_empty (S : OddScale) (n : ℕ) (h : (n+2)%2≠1)
    (x : (state S (n+1)).presentation.X) : IsEmpty (OwnerFiber S (n+2) (Vertex.x x)) := by sorry
