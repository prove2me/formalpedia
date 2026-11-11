-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_distance_le_two_mem_forwardTwo
-- name    : QEC.Coding.BDL26RXInfluenceBounds.distance_le_two_mem_forwardTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:42:33.818086+00:00
-- url     : https://prove2.me/theorems/ace1e24b-cd5b-431f-af41-143232c020d0
-- title:
--   BDL26 RXInfluence Bounds: distance le two mem forward Two
-- statement:
--   Extract the bounded path without assuming that the vertex type has size at least two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L44-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L44-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

theorem QEC.Coding.BDL26RXInfluenceBounds.distance_le_two_mem_forwardTwo (G : DirectedGraph V) (u v : V)
    (h : G.distance u v ≤ (2 : WithTop Nat)) : v ∈ forwardTwo G u := by sorry
