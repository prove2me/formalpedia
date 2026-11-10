-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_rawPositiveFace_planar_image
-- name    : QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_planar_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:38:07.38221+00:00
-- url     : https://prove2.me/theorems/24338c1f-f820-4dc8-9108-8afc62dbe4cf
-- title:
--   BDL26 Replacement Embedding: raw Positive Face planar image
-- statement:
--   All four actual planar corners identify the whole materialized planar image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2277-L2285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2277-L2285

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

theorem QEC.Coding.BDL26ReplacementEmbedding.rawPositiveFace_planar_image (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (i j : Fin S.half)
    (copy a b : BDL26FiniteTannerSquare.Two) :
    rxFaceImage P S J (rawPositiveFace P S f (copy, .inl (i, a), .inl (j, b))) =
      fineQuadrantImage P S J f (2 * (i.val : ℤ) + a.val) (2 * (j.val : ℤ) + b.val) a b := by sorry
