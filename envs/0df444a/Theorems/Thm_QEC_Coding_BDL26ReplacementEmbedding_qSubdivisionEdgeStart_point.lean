-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qSubdivisionEdgeStart_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.qSubdivisionEdgeStart_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:34:56.154376+00:00
-- url     : https://prove2.me/theorems/6e3fa77f-d0c3-408e-9e48-1a9d8bc9e86e
-- title:
--   BDL26 Replacement Embedding: q Subdivision Edge Start point
-- statement:
--   Coordinates of the actual starting vertex of a Q-local path segment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1022-L1031
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1022-L1031

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
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.qSubdivisionEdgeStart_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    qSubdivisionVertexPoint P S J q (qSubdivisionEdgeStart P q S (edge, i)) =
      (1 - 2 * (i.val : ℝ) / S.ell) • J (.q q) +
        (2 * (i.val : ℝ) / S.ell) • J (.z edge.1) := by sorry
