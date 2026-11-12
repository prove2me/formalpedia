-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rx_q_local_edge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rx_q_local_edge_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:34:48.411959+00:00
-- url     : https://prove2.me/theorems/2a608df6-8539-4a80-8979-e2ef7d91040f
-- title:
--   BDL26 Replacement Embedding: rx q local edge midpoint
-- statement:
--   The shifted Q-local edges have exactly the same affine midpoint compatibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3686-L3690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3686-L3690

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementEmbedding
open scoped InnerProductSpace
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26QuantitativeBounds
noncomputable section
open BDL26DecodingGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.rx_q_local_edge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (e : QDoubleCylinderEdge P q S) :
    rxVertexPoint P S J (.z (.inl (.inr ⟨q, e⟩))) = (1 / 2 : ℝ) •
      (rxIntrinsicPoint P S J (.q q) (qDoubleCylinderEdgeStart P q S e) +
       rxIntrinsicPoint P S J (.q q) (qDoubleCylinderEdgeEnd P q S e)) := by sorry
