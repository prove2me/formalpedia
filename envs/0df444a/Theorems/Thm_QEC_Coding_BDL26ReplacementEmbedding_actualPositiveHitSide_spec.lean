-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_actualPositiveHitSide_spec
-- name    : QEC.Coding.BDL26ReplacementEmbedding.actualPositiveHitSide_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:41:19.18038+00:00
-- url     : https://prove2.me/theorems/8a4df90c-ebd7-4c0f-af65-0de76261feba
-- title:
--   BDL26 Replacement Embedding: actual Positive Hit Side spec
-- statement:
--   The selected old triangle really hits the same region and has the correct anchor chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2725-L2737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L2725-L2737

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

theorem QEC.Coding.BDL26ReplacementEmbedding.actualPositiveHitSide_spec (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (c : PositiveCell S) (region : Set E)
    (hhit : (actualFlatImage P S J (f, .inl c) ∩ region).Nonempty) :
    (if actualPositiveHitSide P S J f c region = 0 then c.2.2.val ≤ c.2.1.val
      else c.2.1.val ≤ c.2.2.val) ∧
      (oldTriangleImage P J (f, actualPositiveHitSide P S J f c region) ∩ region).Nonempty := by sorry
