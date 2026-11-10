-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFaceQ1_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ1_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:03:54.093767+00:00
-- url     : https://prove2.me/theorems/7ebfd720-dd69-417a-81fa-354f1553e3c8
-- title:
--   BDL26 Replacement Embedding: old ZFace Q1 point
-- statement:
--   The other actual old-Z Q corner lies on the top boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L493-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L493-L498

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ1_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (oldZFaceQ P S 1 (f, copy)) =
      facePoint P J f (contractionRatio S) 1 := by sorry
