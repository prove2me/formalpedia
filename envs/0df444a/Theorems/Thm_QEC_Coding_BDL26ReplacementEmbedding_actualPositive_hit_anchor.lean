-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositive_hit_anchor
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_anchor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:40:24.407541+00:00
-- url     : https://prove2.me/theorems/d976cf5a-fa9f-4b17-95a6-1641e4020cfa
-- title:
--   BDL26 Replacement Embedding: actual Positive hit anchor
-- statement:
--   The actual positive-family anchor lies within radius two of every unit-ball hit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2601-L2613
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2601-L2613

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_anchor (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S)
    (h₀ : ‖J (.q (P.faceQ f 0)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (h₁ : ‖J (.q (P.faceQ f 1)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz : ‖J (.z (P.faceZ f)) - J (.x (P.faceX f))‖ ≤ S.ell)
    (hz₀ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 0))‖ ≤ S.ell)
    (hz₁ : ‖J (.z (P.faceZ f)) - J (.q (P.faceQ f 1))‖ ≤ S.ell)
    (center : E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ Metric.closedBall center 1).Nonempty) :
    dist (faceFineAnchor P S J f c.2.1.val c.2.2.val) center ≤ 2 := by sorry
