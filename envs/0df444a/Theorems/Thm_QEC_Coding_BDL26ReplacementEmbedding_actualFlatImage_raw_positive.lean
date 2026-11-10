-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatImage_raw_positive
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualFlatImage_raw_positive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:39:06.317568+00:00
-- url     : https://prove2.me/theorems/5df69ad0-4d63-43ff-982c-d7c29d87ec35
-- title:
--   BDL26 Replacement Embedding: actual Flat Image raw positive
-- statement:
--   Reindexing never replaces the actual image by a cardinality-chosen model.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2259-L2264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2259-L2264

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.actualFlatImage_raw_positive (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : RawPositiveCell S) :
    actualFlatImage P S J (f, .inl (rawPositiveCellEquiv S c)) =
      rxFaceImage P S J (rawPositiveFace P S f c) := by sorry
