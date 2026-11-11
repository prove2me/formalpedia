-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rx_local_edge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rx_local_edge_midpoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:34:58.021941+00:00
-- url     : https://prove2.me/theorems/f71e978d-32b1-478e-bb02-1ab989053e84
-- title:
--   BDL26 Replacement Embedding: rx local edge midpoint
-- statement:
--   Each intrinsic X-local edge barycenter is the midpoint of its actual boundary points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3679-L3683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L3679-L3683

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rx_local_edge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (x : P.X) (e : DoubleCylinderEdge P x S) :
    rxVertexPoint P S J (.q (.inl ⟨x, e⟩)) = (1 / 2 : ℝ) •
      (rxIntrinsicPoint P S J (.x x) (tannerDoubleCylinderEdgeStart P x S e) +
       rxIntrinsicPoint P S J (.x x) (tannerDoubleCylinderEdgeEnd P x S e)) := by sorry
