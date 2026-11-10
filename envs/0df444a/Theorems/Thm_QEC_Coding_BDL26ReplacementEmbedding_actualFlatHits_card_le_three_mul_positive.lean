-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualFlatHits_card_le_three_mul_positive
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualFlatHits_card_le_three_mul_positive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:37:09.049028+00:00
-- url     : https://prove2.me/theorems/150e67f3-dce4-4feb-a655-5f3ec57582eb
-- title:
--   BDL26 Replacement Embedding: actual Flat Hits card le three mul positive
-- statement:
--   The factor three counts every actual collapsed label, including coincident images.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1828-L1834
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L1828-L1834

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualFlatHits_card_le_three_mul_positive (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (region : Set E) :
    (familyHits (actualFlatImage P S J) region).card ≤
      3 * (familyHits (fun p : P.Face × PositiveCell S =>
        actualFlatImage P S J (p.1, .inl p.2)) region).card := by sorry
