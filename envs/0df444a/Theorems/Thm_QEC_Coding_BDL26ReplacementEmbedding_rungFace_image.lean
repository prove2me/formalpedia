-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rungFace_image
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rungFace_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:33:00.923982+00:00
-- url     : https://prove2.me/theorems/f6966648-f12c-4b1b-98c6-79c6414fb870
-- title:
--   BDL26 Replacement Embedding: rung Face image
-- statement:
--   The actual zero-area terminal glue face has a constructed segment image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L579-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L579-L588

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rungFace_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P) (edge : QStarEdge P a.1.2)
    (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inr (.inl ⟨a, .inr edge, copy⟩)) =
      segment ℝ
        ((1 - contractionRatio S) • J (.x a.1.1) + contractionRatio S • J (.z edge.1))
        ((1 - contractionRatio S) • J (.q a.1.2) + contractionRatio S • J (.z edge.1)) := by sorry
