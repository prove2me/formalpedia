-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_q_local_edge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_q_local_edge_midpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:36:09.897618+00:00
-- url     : https://prove2.me/theorems/bb3fc515-c2bd-4e2b-8b5a-6fbd574ea473
-- title:
--   BDL26 Replacement Embedding: rz q local edge midpoint
-- statement:
--   The dual shifted Q-local edge center obeys the same concrete endpoint formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3703-L3710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3703-L3710

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_q_local_edge_midpoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (q : P.Q)
    (e : QDoubleCylinderEdge (transposePresentation P) q S) :
    rzVertexPoint P A S J (.x (.inl (.inr ⟨q, e⟩))) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeStart (transposePresentation P) q S e) +
       rzIntrinsicPoint P S J (.q q)
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S e)) := by sorry
