-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_faceFineCorner_vertical_dist
-- name    : QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_vertical_dist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:41:33.923578+00:00
-- url     : https://prove2.me/theorems/99904753-88cd-4788-b6f9-366712f7f71d
-- title:
--   BDL26 Replacement Embedding: face Fine Corner vertical dist
-- statement:
--   Each vertical fine side is likewise an actual unit step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2980-L2988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2980-L2988

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem QEC.Coding.BDL26ReplacementEmbedding.faceFineCorner_vertical_dist (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hgeo : IncomingFaceGeometry P S J lower width)
    (f : P.Face) (m n : ℤ) (a b : BDL26FiniteTannerSquare.Two) :
    dist (faceFineCorner P S J f m n a b) (faceFineCorner P S J f m n a (1 - b)) ≤ 1 := by sorry
