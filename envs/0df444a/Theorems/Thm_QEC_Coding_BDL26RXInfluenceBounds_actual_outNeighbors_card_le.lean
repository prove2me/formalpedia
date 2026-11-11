-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_actual_outNeighbors_card_le
-- name    : QEC.Coding.BDL26RXInfluenceBounds.actual_outNeighbors_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:58:43.53642+00:00
-- url     : https://prove2.me/theorems/40b25840-802b-46b5-a40b-e5e4d9acdd86
-- title:
--   BDL26 RXInfluence Bounds: actual out Neighbors card le
-- statement:
--   Measured actual Tanner degree bounds outgoing edges; directed symmetry is unused.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L89-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L89-L106

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
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.actual_outNeighbors_card_le
    (u : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z) :
    (outNeighbors (rxData S depth i h).levelGraph.graph u).card ≤ 7 := by sorry
