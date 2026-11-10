-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRXHits_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:07:23.030075+00:00
-- url     : https://prove2.me/theorems/793279d7-dc81-4eb4-8a71-95c204da9f47
-- title:
--   BDL26 Replacement Embedding: actual RXHits card le
-- statement:
--   Every actual RX face label, including all zero-area seams, obeys the derived packing count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2812-L2832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2812-L2832

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualRXHits_card_le (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rxFaceImage P S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by sorry
