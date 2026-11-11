-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_readRegion_iff_distance
-- name    : QEC.Coding.BDL26RXInfluenceBounds.readRegion_iff_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:44:17.771476+00:00
-- url     : https://prove2.me/theorems/b12a086b-d12d-4b16-8a82-51e870eef0d3
-- title:
--   BDL26 RXInfluence Bounds: read Region iff distance
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the read Region iff distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L125-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L125-L138

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

theorem QEC.Coding.BDL26RXInfluenceBounds.readRegion_iff_distance (p : FamilyZ S depth i.succ) (z : FamilyZ S depth i.castSucc) :
    p ∈ readRegion S depth i h z ↔
      DirectedGraph.distance (rxData S depth i h).levelGraph.graph
        ((rxData S depth i h).topCenter p) ((rxData S depth i h).coarseCenter z) ≤ 2 := by sorry
