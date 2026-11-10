-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rungFaceQ1_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rungFaceQ1_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:32:23.603814+00:00
-- url     : https://prove2.me/theorems/5312695e-34d5-49d4-b062-53b4acfbc454
-- title:
--   BDL26 Replacement Embedding: rung Face Q1 point
-- statement:
--   The other endpoint of a terminal-rung glue face belongs to the Q-local path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L560-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L560-L565

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rungFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (glueFaceQ1 P S ⟨a, .inr edge, copy⟩) =
      (1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1) := by sorry
