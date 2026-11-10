-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rectangle_image_subset_glue
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rectangle_image_subset_glue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:33:02.606787+00:00
-- url     : https://prove2.me/theorems/1bd17fb2-df01-49f3-bb14-6be99045a36a
-- title:
--   BDL26 Replacement Embedding: rectangle image subset glue
-- statement:
--   A materialized boundary-rectangle quadrant is contained in the adjacent actual
--   Q-path glue face. The subset follows from their shared endpoint and midpoint tags.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1226-L1243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1226-L1243

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rectangle_image_subset_glue (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (a : XQEdge P)
    (edge : QSubdivisionEdge P a.1.2 S)
    (copy endpoint : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inl ⟨a.1.1,
        .inr (qToXSubdivisionBoundaryEdge P a.1.2 a.1.1 a.2 S edge), copy, endpoint⟩) ⊆
      rxFaceImage P S J (.inr (.inl ⟨a, .inl (copy, edge), endpoint⟩)) := by sorry
