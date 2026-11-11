-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_qSubdivisionEdge_midpoint
-- name    : QEC.Coding.BDL26ReplacementEmbedding.qSubdivisionEdge_midpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:32:46.739793+00:00
-- url     : https://prove2.me/theorems/0f1eaad3-22f7-4d71-9b84-dba7cbe9cf74
-- title:
--   BDL26 Replacement Embedding: q Subdivision Edge midpoint
-- statement:
--   Both endpoints determine the actual Q-path segment midpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1046-L1054
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1046-L1054

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

theorem QEC.Coding.BDL26ReplacementEmbedding.qSubdivisionEdge_midpoint (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (q : P.Q) (edge : QStarEdge P q) (i : Fin S.half) :
    (1 / 2 : ℝ) •
      (qSubdivisionVertexPoint P S J q (qSubdivisionEdgeStart P q S (edge, i)) +
       qSubdivisionVertexPoint P S J q (qSubdivisionEdgeEnd P q S (edge, i))) =
      (1 - (2 * (i.val : ℝ) + 1) / S.ell) • J (.q q) +
        ((2 * (i.val : ℝ) + 1) / S.ell) • J (.z edge.1) := by sorry
