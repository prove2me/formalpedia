-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rz_local_edge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rz_local_edge_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T21:38:04.303676+00:00
-- url     : https://prove2.me/theorems/8db53bad-746d-4acd-8642-5cf04b9dc43e
-- title:
--   BDL26 Replacement Embedding: rz local edge midpoint
-- statement:
--   The dual Z-local edge center has its actual intrinsic endpoints as affine midpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3694-L3700
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3694-L3700

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rz_local_edge_midpoint (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) (z : P.Z) (e : ZDoubleCylinderEdge P z S) :
    rzVertexPoint P A S J (.q (.inl ⟨z, e⟩)) = (1 / 2 : ℝ) •
      (rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeStart (transposePresentation P) z S e) +
       rzIntrinsicPoint P S J (.z z)
        (tannerDoubleCylinderEdgeEnd (transposePresentation P) z S e)) := by sorry
