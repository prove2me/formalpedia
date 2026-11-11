-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_forwardTwo_card_le
-- name    : QEC.Coding.BDL26RXInfluenceBounds.forwardTwo_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:43:24.333555+00:00
-- url     : https://prove2.me/theorems/c251f8ca-76a9-4ef2-a5bf-6e0d058e3248
-- title:
--   BDL26 RXInfluence Bounds: forward Two card le
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the forward Two card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L65-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L65-L78

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

theorem QEC.Coding.BDL26RXInfluenceBounds.forwardTwo_card_le (G : DirectedGraph V)
    (hdegree : ∀ u, (outNeighbors G u).card ≤ 7) (u : V) :
    (forwardTwo G u).card ≤ 57 := by sorry
