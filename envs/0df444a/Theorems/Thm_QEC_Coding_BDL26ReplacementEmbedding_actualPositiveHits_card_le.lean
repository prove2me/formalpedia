-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositiveHits_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualPositiveHits_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:40:51.4536+00:00
-- url     : https://prove2.me/theorems/79894116-465e-49f1-97c0-5cbb048c84aa
-- title:
--   BDL26 Replacement Embedding: actual Positive Hits card le
-- statement:
--   Actual positive labels are packed over only those original triangle labels hit by the ball.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2758-L2804
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2758-L2804

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualPositiveHits_card_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E) :
    ((familyHits (fun p : P.Face × PositiveCell S => actualFlatImage P S J (p.1, .inl p.2))
      (Metric.closedBall center 1)).card : ℝ) ≤
      ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) *
        (16 * Real.pi * S.ell ^ 2 / (lower * width)) := by sorry
