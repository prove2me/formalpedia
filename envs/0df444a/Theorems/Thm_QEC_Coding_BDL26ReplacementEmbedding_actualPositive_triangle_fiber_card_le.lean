-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositive_triangle_fiber_card_le
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualPositive_triangle_fiber_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:41:25.197533+00:00
-- url     : https://prove2.me/theorems/2f928e48-c86e-4172-8b09-2db011ec92b5
-- title:
--   BDL26 Replacement Embedding: actual Positive triangle fiber card le
-- statement:
--   The count is derived for an actual materialized face family in one incoming triangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2639-L2690
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2639-L2690

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualPositive_triangle_fiber_card_le (P : TannerSquarePresentation)
    (S : OddScale) (J : Vertex P → E) (f : P.Face)
    (side : BDL26FiniteTannerSquare.Two) (s : Finset (PositiveCell S))
    (center : E) {lower width : ℝ} (hlower : 0 < lower) (hwidth : 0 < width)
    (hb : lower ≤ ‖J (.q (P.faceQ f side)) - J (.x (P.faceX f))‖)
    (hc : lower ≤ ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖)
    (hbc : lower ≤ ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f side))‖)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (hthin : TriangleWidthAtLeast
      (J (.q (P.faceQ f side)) - J (.x (P.faceX f)))
      (J (.z (P.faceZ f)) - J (.x (P.faceX f))) width)
    (hchart : ∀ c ∈ s, if side = 0 then c.2.2.val ≤ c.2.1.val
      else c.2.1.val ≤ c.2.2.val)
    (hhit : ∀ c ∈ s,
      (actualFlatImage P S J (f, .inl c) ∩ Metric.closedBall center 1).Nonempty) :
    (s.card : ℝ) ≤ 16 * Real.pi * S.ell ^ 2 / (lower * width) := by sorry
