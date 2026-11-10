-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositive_hit_incoming
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_incoming
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:39:44.580726+00:00
-- url     : https://prove2.me/theorems/591bb5bf-c91e-4fe7-8e06-9906683dfb85
-- title:
--   BDL26 Replacement Embedding: actual Positive hit incoming
-- statement:
--   Every actual positive-cell hit is assigned to a hit incoming triangle in its actual chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2575-L2598
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2575-L2598

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualPositive_hit_incoming (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ region).Nonempty) :
    (c.2.2.val ≤ c.2.1.val ∧ (oldTriangleImage P J (f, 0) ∩ region).Nonempty) ∨
      (c.2.1.val ≤ c.2.2.val ∧ (oldTriangleImage P J (f, 1) ∩ region).Nonempty) := by sorry
