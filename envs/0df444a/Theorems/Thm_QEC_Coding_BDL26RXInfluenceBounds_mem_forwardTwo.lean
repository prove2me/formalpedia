-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_mem_forwardTwo
-- name    : QEC.Coding.BDL26RXInfluenceBounds.mem_forwardTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:58:27.689993+00:00
-- url     : https://prove2.me/theorems/df6e8092-44c7-41b0-894d-33e3646efeb1
-- title:
--   BDL26 RXInfluence Bounds: mem forward Two
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the mem forward Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L33-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L33-L37

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

theorem QEC.Coding.BDL26RXInfluenceBounds.mem_forwardTwo (G : DirectedGraph V) (u v : V) :
    v ∈ forwardTwo G u ↔ v = u ∨ G.edge u v = true ∨
      ∃ w, G.edge u w = true ∧ G.edge w v = true := by sorry
