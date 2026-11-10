-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFace_image
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFace_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:26:56.406645+00:00
-- url     : https://prove2.me/theorems/717d6bc2-909d-4c0c-b969-1c2a86f749f4
-- title:
--   BDL26 Replacement Embedding: old ZFace image
-- statement:
--   The actual old-Z family realizes the terminal fine-grid square, not just its count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L515-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L515-L521

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFace_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (.inr (.inr (f, copy))) =
      positiveImage S (faceGrid P S J f) (copy, lastStrip S, lastStrip S) := by sorry
