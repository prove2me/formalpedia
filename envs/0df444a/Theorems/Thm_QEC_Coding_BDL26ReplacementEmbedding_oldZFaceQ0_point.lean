-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementEmbedding_oldZFaceQ0_point
-- name    : QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ0_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:03:39.401758+00:00
-- url     : https://prove2.me/theorems/8bf5ae7d-5733-47e0-82ef-be9ab3b93bbc
-- title:
--   BDL26 Replacement Embedding: old ZFace Q0 point
-- statement:
--   The actual old-Z face Q0 lies on the right boundary, including its one-step offset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L485-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbeddingCoordinates.lean#L485-L490

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

theorem QEC.Coding.BDL26ReplacementEmbedding.oldZFaceQ0_point (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → E) (f : P.Face) (copy : BDL26FiniteTannerSquare.Two) :
    rxOnePoint P S J (oldZFaceQ P S 0 (f, copy)) =
      facePoint P J f 1 (contractionRatio S) := by sorry
