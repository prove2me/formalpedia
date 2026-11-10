-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rungFaceZ_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rungFaceZ_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:32:51.36328+00:00
-- url     : https://prove2.me/theorems/69ea8298-444e-43a2-a6f7-d09e16a2b598
-- title:
--   BDL26 Replacement Embedding: rung Face Z point
-- statement:
--   The Q-local vertical edge also collapses, while its domain label remains distinct.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L568-L576
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L568-L576

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rungFaceZ_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxTwoPoint P S J (glueFaceZ P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1) := by sorry
