-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualRZHits_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:41:29.867969+00:00
-- url     : https://prove2.me/theorems/8bb2993d-fb73-4002-8c68-35b16b912f32
-- title:
--   BDL26 Replacement Embedding: actual RZHits card le
-- statement:
--   The actual RZ density estimate uses precisely the same incoming labeled triangle family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2946-L2961
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2946-L2961

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualRZHits_card_le (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (J : Vertex P → E) {lower width tPrime : ℝ}
    (hlower : 0 < lower) (hwidth : 0 < width)
    (hgeo : IncomingFaceGeometry P S J lower width) (center : E)
    (hincoming : ((familyHits (oldTriangleImage P J) (Metric.closedBall center 1)).card : ℝ) ≤ tPrime) :
    ((familyHits (rzFaceImage P A S J) (Metric.closedBall center 1)).card : ℝ) ≤
      48 * Real.pi * tPrime * S.ell ^ 2 / (lower * width) := by sorry
